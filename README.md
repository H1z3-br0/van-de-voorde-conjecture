# A proof of Van de Voorde's conjecture on conics and sets without tangents

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23670082.svg)](https://doi.org/10.5281/zenodo.23670082)

This repository contains the paper

> I. A. Chobanov, *Conics and (q+1)/2 exterior points forming a set without tangents: a proof of a
> conjecture of Van de Voorde*, preprint (2026)

together with every computation it relies on and a Lean 4 formalisation of the main argument.

## The result in short

Take a conic C in the projective plane over a finite field with q elements, q odd. A point is
*exterior* if it lies on two tangents of C. Choose (q+1)/2 exterior points and call this set S. When
does no line of the plane meet C ∪ S in exactly one point?

In 2011 Geertrui Van de Voorde conjectured that this happens only for q = 7 and q = 11. We prove this:
apart from the trivial case q = 3, such sets S exist only for q = 7 and q = 11, and for these two
values S is unique up to symmetry, with symmetry group S4 and A5 respectively.

## What is in the repository

| Path | Content |
|---|---|
| `vdv_conjecture.pdf` | the paper |
| `main.tex`, `refs.bib`, `build.sh` | its LaTeX source; `sh build.sh` rebuilds the PDF |
| `supplement/` | Python scripts that check every step of the proof on concrete fields, the search program behind the computer data, and the data itself ([details](supplement/README.md)) |
| `supplement/lean/BSWCheck/` | the Lean 4 project that machine-checks the main line of the proof ([details](supplement/lean/BSWCheck/README.md)) |
| `.github/workflows/checks.yml` | runs all of the above automatically on GitHub after every change |
| `CITATION.cff` | how to cite this work |

## How to check the results yourself

**Computations** (Python 3 and a C compiler, under a minute):

```sh
sh supplement/run_all.sh
```

**Formal proof** (needs [elan](https://github.com/leanprover/elan); the first run downloads a few GB
of compiled Mathlib):

```sh
cd supplement/lean/BSWCheck
lake exe cache get
sh scripts/check.sh
```

The formal proof assumes, as explicit hypotheses, three classical results that are not yet in
Mathlib: Stickelberger's theorem (in the form of Proposition 6.2 of the paper), Weil's bound for
character sums, and McConnel's theorem. Everything else is proved from scratch. The Lean README
lists exactly which statements of the paper are formalised.

**Paper:** `sh build.sh` (needs a standard TeX distribution with `pdflatex` and `bibtex`).

## Licence

The code (Python, C, Lean, shell scripts) is released under the MIT licence (`LICENSE`); the text of
the paper under CC BY 4.0 (`LICENSE-text.md`).

## Contact

I. A. Chobanov, cobanovimam752@gmail.com, ORCID [0009-0001-1401-6527](https://orcid.org/0009-0001-1401-6527).
The author is a high-school student at AESC MSU (Kolmogorov's boarding school of Moscow State University); the work was
done independently.
