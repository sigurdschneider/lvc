OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc -v 
INCLUDES=
OCAMLFLAGS=$(INCLUDES) -annot
OCAMLOPTFLAGS=$(INCLUDES) -annot
OCAMLLEXFLAGS=
OCAMLYACCFLAGS=

YACC_OBJS = lexer.ml parser.ml

PROG_OBJS= big.cmx names.cmx lvc.cmx util.cmx lexer.cmx parser.cmx pmove.cmx main.cmx 

all: $(PROG_OBJS)
	$(OCAMLOPT) -o lvc nums.cmxa $(OCAMLFLAGS) $(PROG_OBJS)

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mly .mll

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c  $<

.mll.ml:
	$(OCAMLLEX) $(OCAMLLEXFLAGS) $<

.mly.ml:
	$(OCAMLYACC) $(OCAMLYACCFLAGS) $<

clean:
	rm -f lvc
	rm -f *.cm[iox]
	rm -f *.o
	rm -f *.annot
	rm lexer.ml
	rm -rf lexer.mli
	rm parser.ml
	rm -rf parser.mli
	rm .depend

.depend: $(YACC_OBJS)
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend
