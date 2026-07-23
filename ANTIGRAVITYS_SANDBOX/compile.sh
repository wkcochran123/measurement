#!/bin/bash
set -e
cd "$(dirname "$0")"
echo "Compiling book.tex with pdflatex (Pass 1)..."
/Library/TeX/texbin/pdflatex -interaction=nonstopmode book.tex
echo "Compiling book.tex with pdflatex (Pass 2)..."
/Library/TeX/texbin/pdflatex -interaction=nonstopmode book.tex
echo "Compilation complete! book.pdf is generated."
