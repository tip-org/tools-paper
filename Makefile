TARGETS=paper.pdf

all: $(TARGETS)

clean:
	rm -f $(TARGETS)

.PHONY: all clean

TEMPLATE=latex.template
BIBFILE=bibfile.bib
FILTER=./Filter.hs

%.tex: %.md $(TEMPLATE) $(BIBFILE) $(FILTER)
	pandoc $< -o $@ --template $(TEMPLATE) --standalone --filter $(FILTER) --bibliography=$(BIBFILE)

paper.pdf: paper.tex
	latexmk -pdf $<
