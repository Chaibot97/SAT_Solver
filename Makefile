cython:
	python setup.py build_ext --inplace

clean:
	rm -rf dpll.c dpll.*.so