dir=src

cython:
	python setup.py build_ext --build-lib $(dir)

clean:
	(cd $(dir) && rm -rf *.c *.so *.html)
	