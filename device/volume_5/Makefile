
MAIN = names
TEXBIN = /Library/TeX/texbin
LATEXMK = $(TEXBIN)/latexmk

all:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(LATEXMK) -C

distclean: clean
	rm -f $(MAIN).pdf

.PHONY: all clean distclean
