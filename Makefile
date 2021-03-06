TARGETS=paper.pdf

all: $(TARGETS)

clean:
	rm -f $(TARGETS) paper.tex paper.aux paper.blg paper.bbl paper.bcf

.PHONY: all clean

TEMPLATE=latex.template
BIBFILE=bibfile.bib
FILTER=./Filter

./Filter: Filter.hs
	ghc --make Filter.hs

%.tex: %.md $(TEMPLATE) $(BIBFILE) $(FILTER) $(glob *.smt2)
	pandoc $< -o $@ --template $(TEMPLATE) --standalone --filter $(FILTER) --bibliography $(BIBFILE) --biblatex

paper.pdf: paper.tex $(BIBFILE)
	latexmk -pdf $<
