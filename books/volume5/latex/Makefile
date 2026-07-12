
MAIN = volume5
TEXBIN = /Library/TeX/texbin

all:
	$(TEXBIN)/latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(TEXBIN)/latexmk -C

distclean: clean
	rm -f $(MAIN).pdf

.PHONY: all clean distclean
