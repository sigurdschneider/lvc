.PHONY: all

all:
	ocamlbuild -use-ocamlfind -package num lvcc.native

clean:
	ocamlbuild -clean

tests: all
	./lvc.native
