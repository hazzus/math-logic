.PHONY: pack all run clean

COMPILER=ghc
OPTIONS=-O3 -outputdir out -o out/main
SOURCES=$(shell find src app -type f -name "*.hs")

all: out
	$(COMPILER) $(OPTIONS) $(SOURCES)

run:
	./out/main

out:
	mkdir -p out

pack:
	zip hw4.zip -r Makefile $(SOURCES)

clean:
	rm -rf out
