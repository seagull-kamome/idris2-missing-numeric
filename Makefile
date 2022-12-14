
PKG=missing-numeric
DEP=-p contrib -p elab-util -p sop


build:
	idris2 --build ${PKG}.ipkg

install:
	idris2 --install ${PKG}.ipkg

clean:
	idris2 --clean ${PKG}.ipkg
	rm -rf build

distclean:
	find . -name *~ -delete
	find . -name *.bak -delete

check: check-chez check-gambit check-node check-js check-refc
check-chez:
	idris2 -p ${PKG} ${DEP} tests/Main.idr --cg chez -x main
check-gambit:
	# idris2 -p ${PKG} ${DEP} tests/Main.idr --cg gambit -x main
check-node:
	idris2 -p ${PKG} ${DEP} tests/Main.idr --cg node -x main
check-js:
	idris2 -p ${PKG} ${DEP} tests/Main.idr --cg javascript -o test-javascript.js
check-refc:
	idris2 -p ${PKG} ${DEP} tests/Main.idr --cg refc -o test-refc
	build/exec/test-refc

.PHONY: clean deepclean build install check

