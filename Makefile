TARGETS=paper.pdf

all: $(TARGETS)

clean:
	rm -f $(TARGETS) paper.tex

.PHONY: all clean

TEMPLATE=latex.template
BIBFILE=bibfile.bib
FILTER=./Filter.hs

%.tex: %.md $(TEMPLATE) $(BIBFILE) $(FILTER) *smt2
	pandoc $< -o $@ --template $(TEMPLATE) --standalone --filter $(FILTER) --bibliography $(BIBFILE) --biblatex

paper.pdf: paper.tex
	latexmk -pdf $<
