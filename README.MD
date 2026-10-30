paper/   LaTeX source. main.tex uses REVTeX 4.2 (aps, prd, preprint) when installed, e.g. on arXiv,
         and falls back to the article class otherwise. Build: pdflatex main; bibtex main; pdflatex main x2.
         body.tex is generated from the Markdown master; main.bbl is included for arXiv.
lean/    Lean 4 (v4.36.0-rc1) + Mathlib files, namespace CausalDensification; compile with `lake env lean <file>`.
           UndampedKernelConstants.lean  constants of Theorem 18 (Lemmas L1, L2)
           PosetLimitCore.lean           Theorem 17 (pairs), summability for Theorem 19, Polya bounds for Theorem 20
           PosetLimitFramework.lean      Theorem 17 (general k, torus), Fatou step, Doeblin ergodicity, martingale a.s. convergence
           DefectGasAlgebra.lean         Theorem 21: factorisation, Jensen, inner Jensen, lock window
           DefectGasLimit.lean           Theorem 21: Fubini step, Mahler positivity, null zero set, strong-law substitution
step80/  Scripts for the phase-uniformity, larger-M overlap and isomorphism checks of Sec. VII E.
