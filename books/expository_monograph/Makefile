MAIN = measurement.tex
OUTDIR = build
TEXBIN = /Library/TeX/texbin

all:
	export PATH=$(TEXBIN):$$PATH && export BIBINPUTS=$(shell pwd)/../../instrument:$$BIBINPUTS && cd latex && latexmk -pdf -outdir=$(OUTDIR) -interaction=nonstopmode -halt-on-error $(MAIN)

clean:
	export PATH=$(TEXBIN):$$PATH && cd latex && latexmk -C -outdir=$(OUTDIR) $(MAIN)

distclean: clean
	rm -f latex/build/measurement.pdf

.PHONY: all clean distclean
