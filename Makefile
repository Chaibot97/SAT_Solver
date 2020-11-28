dir=src

cython:
	python setup.py build_ext --build-lib $(dir)

clean:
	rm -rf src/*.c sr/c*.so src/*.html
	rm -rf build