# LVC Compiler Project
IL - IL/I, IL/F and Coherence

Translation validation for register assignment and SSA construction

LVC stands for Linear Verified Compiler.

## Dependencies

- **Coq**

    Sources compile with Coq version 8.4pl4 (May 2014).

- **Coq Containers Plugin**

    You need to have the containers library installed:
		http://www.lix.polytechnique.fr/coq/pylons/contribs/view/Containers/v8.4

- **OCaml** (including ocamlbuild)

    Sources compile with ocaml version 3.12.1. OCaml should include ocamlbuild.

- **menhir**

    A parser generator mostly compatible with ocamlyacc (but better at explaining conflicts):
    http://gallium.inria.fr/~fpottier/menhir/

- **ruby** [optional]

    If you want build times to be output, you need ruby.

## Building LVC

After installing the dependencies, use

	configure.sh

to generate a Makefile (use `configure.sh --vanilla` if you don't have ruby installed). Then build LVC using

	make

This will generate a binary

	extraction/lvcc.native

There are some example files in extraction/examples. Run one by issuing the following command:

	cd extraction
	./lvcc.native examples/foo.il
