# Grothendieck's rank-\p^2 group-scheme conjecture

This repository collects the focused work on Grothendieck's question:

> Is every finite locally free group scheme of order `n` annihilated by `n`?

The central case here is rank `p^2`, especially rank `4` in residue
characteristic `2`, together with the explicit constructions and audits that
led to the current rank-`p^2` counterexample formalizations.

## Contents

- `docs/`: core mathematical reports and handoff notes;
- `notes/`: source notes and TeX manuscripts for the rank-4 and rank-`p^2`
  constructions;
- `lean/`: Lean formalizations and their toolchain metadata;
- `scripts/`: Python verification and search programs;
- `m2/`: Macaulay2 calculations;
- `handoff/`: supporting rank-4 theory and reproducibility material.

Generated logs, caches, scratch directories, run outputs, ZIP archives, and
LaTeX intermediates were intentionally left out. Rendered documents can be
regenerated from the retained TeX sources where applicable.

## Provenance

The files were curated from the larger `FiniteFlatGroupSchemes` workspace on
2026-07-13. The original workspace was not modified by this curation.
