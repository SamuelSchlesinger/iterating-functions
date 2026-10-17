.PHONY: all check lean-check clean

all: iterated_function_circuits.pdf

iterated_function_circuits.pdf: iterated_function_circuits.tex
	pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex
	pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex
	pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex

check:
	python3 verify_small_instances.py
	python3 verify_extensions.py
	python3 verify_sparse_counter.py
	python3 verify_checkpoint_sets.py

lean-check:
	cd lean && lake build --wfail

clean:
	rm -f iterated_function_circuits.aux iterated_function_circuits.log iterated_function_circuits.out
