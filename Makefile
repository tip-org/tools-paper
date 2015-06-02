TARGETS=paper.tex

all: $(TARGETS)

clean:
	rm -f $(TARGETS)

.PHONY: all clean

%.tex: %.md
	pandoc $< -o $@ --standalone --filter ./Filter.hs --bibliography=bibfile.bib

