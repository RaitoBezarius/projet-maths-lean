#!/usr/bin/env bash
pandoc rapport.md --pdf-engine=xelatex -so rapport.tex
latexmk -xelatex -latexoption=-shell-escape rapport.tex
latexmk -c -xelatex -latexoption=-shell-escape rapport.tex
rm rapport.tex rapport.xdv
rm -r _minted-rapport
