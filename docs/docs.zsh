#!/bin/zsh

rm -rf html
mkdir html

agda --html --html-dir=html --html-highlight=auto Causality/CausalGraph.lagda.md
cp docs/Agda.css html

for file in html/**/*.md
do
  pandoc "$file" -o "${file%.md}.html" --citeproc --bibliography=docs/bibliography/causality.bib --csl=docs/bibliography/ieee.csl --mathjax --css=Agda.css --standalone
done
