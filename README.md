# LVC Compiler Project
LVC stands for Linear Verified Compiler. The compiler is based on the linear first-order language IL [1].

## Dependencies

- **Coq**

    Sources compile with Coq version 8.4pl4 (May 2014).

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
	make extraction

This will generate a binary

	extraction/lvcc.native

There are some example files in extraction/examples. Run one by issuing the following command:

	cd extraction
	./lvcc.native examples/dve.il
	./lvcc.native examples/dve+dce.il

All source files are interpreted as IL/I. Translation to IL/F is supported via argument "-c true".

## Disclaimer

The sources incorporate ideas and code from various sources.

- The subdir `Containers` contains a copy of the [Containers library](http://www.lix.polytechnique.fr/coq/pylons/contribs/view/Containers/v8.4) which was slightly adapted for the needs of the project.
- The subdir `paco` contains a copy of the [Paco Library](http://plv.mpi-sws.org/paco/).
- The subdir TransVal/ contains work based on Heiko Becker's Bachelor's Thesis: [Verified SMT-based Translation Validation](http://compilers.cs.uni-saarland.de/publications/theses/becker_bsc.pdf).
- The file `Lattice.v` was inspired by the [Lattice development from Daniel W.H. James and Ralf Hinze](http://www.cs.ox.ac.uk/people/daniel.james/lattice.html).
- The file `Infra/SizeInduction.v` contains the type-class based size-induction from [AutoSubst](https://www.ps.uni-saarland.de/autosubst/).

## References

[1] Sigurd Schneider. 'Semantics of an Intermediate Language for Program Transformation'. Master's Thesis. Saarland University, 2013.
