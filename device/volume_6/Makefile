MAIN = volume6
TEXBIN = /Library/TeX/texbin
LATEXMK = $(TEXBIN)/latexmk
BIBINPUTS = .:../../instrument:

all:
	BIBINPUTS=$(BIBINPUTS) $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(LATEXMK) -C

distclean: clean
	rm -f $(MAIN).pdf

.PHONY: all clean distclean
