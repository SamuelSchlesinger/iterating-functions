.PHONY: all check clean

all: iterated_function_circuits.pdf

iterated_function_circuits.pdf: iterated_function_circuits.tex
	pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex
	pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex
	pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex

check:
	python3 verify_small_instances.py

clean:
	rm -f iterated_function_circuits.aux iterated_function_circuits.log iterated_function_circuits.out
