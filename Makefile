 
TEX=pdflatex
all:
	latexmk -pdf -interaction=nonstopmode paper.tex
clean:
	latexmk -C
