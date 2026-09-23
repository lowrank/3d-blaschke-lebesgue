#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build/main build/continuation
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/main volume_bound_04144.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/main volume_bound_04144.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/main volume_bound_04144.tex
cp build/main/volume_bound_04144.pdf volume_bound_04144.pdf
cd continuation
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build/continuation quadratic_support_program.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build/continuation quadratic_support_program.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build/continuation quadratic_support_program.tex
cp ../build/continuation/quadratic_support_program.pdf quadratic_support_program.pdf
