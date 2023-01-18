SHELL=/bin/bash
BNFC?=/home/students/inf/PUBLIC/MRJP/bin/bnfc
all:
	-mkdir build
	cd src && \
	$(BNFC) --functor Latte.cf && \
	happy -gca ParLatte.y && \
	alex -g LexLatte.x && \
	ghc --make Main.hs -odir ../build -hidir ../build -o ../latc_llvm

clean:
	-rm -rf build
	-rm -f src/{DocLatte,LexLatte,ParLatte,SkelLatte,PrintLatte,AbsLatte,ErrM,TestLatte}.*
	-rm -f latc_llvm
