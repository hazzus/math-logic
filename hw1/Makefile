.PHONY: pack all run clean

COMPILER=ghc
OPTIONS=--make -dynamic -O3 -i./src:lib -Ilib -outputdir out -o out/main
SOURCES=$(shell find src app lib -type f -name "*.hs")

all: out
	$(COMPILER) $(OPTIONS) app/Main.hs

run:
	./out/main

out:
	mkdir -p out

pack:
	zip hw1.zip -r Makefile $(SOURCES)

clean:
	rm -rf out
