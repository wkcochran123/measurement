LATEXMK ?= latexmk

.PHONY: pdf clean

pdf:
	cd latex && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error grammar_of_measurement.tex

clean:
	cd latex && $(LATEXMK) -C grammar_of_measurement.tex

