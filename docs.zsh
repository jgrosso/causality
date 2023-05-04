#!/bin/zsh

rm -rf docs
mkdir docs

agda --html --html-dir=docs --html-highlight=auto Causality/CausalGraph.lagda.md
cp -R assets/{index.html,Agda.css} docs

for file in docs/**/*.md
do
  pandoc "$file" -o "${file%.md}.html" --citeproc --bibliography=assets/bibliography/causality.bib --csl=assets/bibliography/ieee.csl --mathjax --css=Agda.css --standalone
done
