SRC = src/vcgen.scala
GC = src/gc.scala # Guarded Commands, not gcc
WP = src/wp.scala
UTIL = src/util.scala

all: compile run

compile:
	-[ -e classes ] || mkdir classes
	scalac -d classes ${SRC} ${GC} ${UTIL} ${WP}

run: 
	scala -cp classes VCGen imp/simple.imp

help:
	@echo "This script compiles the file(s) ${SRC} ${GC} ${UTIL} ${WP}"
	@echo "Compiled classes are stored in the classes/ directory"
	@echo ""
	@echo "To run the example parser on a file use the"
	@echo "following syntax:"
	@echo ""
	@echo "    scala -cp classes VCGen imp/count.imp"
	@echo ""

.PHONY: all help
