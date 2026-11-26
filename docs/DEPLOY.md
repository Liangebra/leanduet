# Deployment

## Online editor

GitHub Pages serves only the contents of web/. The static workbench cannot execute Lean or call an AI provider.

In Settings → Pages, select GitHub Actions. The Deploy browser-only demo workflow runs on pushes to main and manual dispatch. It runs JavaScript tests and an independent Chromium test of the static site at a project-style /leanduet/ prefix, including the three-language about page. It then publishes the tested checkout. Superseded runs are cancelled or skip publication. The full Tests workflow separately checks Python, Lean, semantic extraction and real local browser integration. A static deployment does not imply that the local backend has passed.

- Editor: https://liangebra.github.io/leanduet/
- About: https://liangebra.github.io/leanduet/about.html
- Documentation fallback: README.md, README.zh-CN.md, README.ja.md in the repository.

A workflow that reports success with a skipped Deploy step is not a successful publication. Inspect the Deploy step and its page URL.

## Local server

Run python server.py. Use --project for a built compatible Lean project. Run only trusted Lean source; this is not a sandbox. See docs/RESEARCH.md for the current limits.
