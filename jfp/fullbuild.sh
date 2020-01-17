#!/bin/bash
lhs2TeX der-monad.lhs > der-monad.tex
pdflatex der-monad.tex
bibtex der-monad.aux
pdflatex der-monad.tex
pdflatex der-monad.tex
