MAIN = measurement
TEXBIN = /Library/TeX/texbin
LATEXMK = $(TEXBIN)/latexmk

all:
	BIBINPUTS=.:../../instrument: $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	$(LATEXMK) -C $(MAIN).tex

distclean: clean
	rm -f $(MAIN).pdf

.PHONY: all clean distclean
