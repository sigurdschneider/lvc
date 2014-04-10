.PHONY: all

all:
	ocamlbuild -use-ocamlfind -package num lvc.native

clean:
	ocamlbuild -clean

tests: all
	./lvc.native
