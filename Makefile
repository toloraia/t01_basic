all: src/code
.PHONY: all

src/example: src/code.c
	gcc -Wno-attributes -o $@ $<

clean:
	rm -f src/code
.PHONY: clean
