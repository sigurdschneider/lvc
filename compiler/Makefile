.PHONY: all

# add --table to menhir flags for table (instead of recursive descend) which is probably faster.
all:
	ocamlbuild -classic-display -use-ocamlfind -use-menhir -menhir "menhir --explain --infer -la 1" lvcc.byte

debug:
	ocamlbuild -classic-display -use-ocamlfind -use-menhir -menhir "menhir --explain --infer -la 1" lvcc.d.byte

clean:
	ocamlbuild -clean

tests: all
	./lvc.native
