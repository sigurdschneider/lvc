# LVC Compiler Project
LVC stands for Linear Verified Compiler. The compiler is based on the linear first-order language IL [1,2]. The goal of the project is to show that functional SSA, i.e. using a functional style lexical variable binding provides for a viable semantic foundation for static single assignment (SSA).

- CoqDoc documentation is available [here](https://sigurdschneider.github.io/lvc).

## Dependencies

- **Coq**

    Sources compile with Coq version 8.7.2 (March 2018). Other versions might work.

- **OCaml** (including ocamlbuild)

    Sources compile with ocaml version 4.04.2, other versions might work.
    OCaml should include ocamlbuild.

- **menhir**

    A parser generator mostly compatible with ocamlyacc (but better at explaining conflicts):
    http://gallium.inria.fr/~fpottier/menhir/
    Sources compile with version 20171013. Other versions might work.

- **ruby** [optional]

    If you want build times to be output, you need ruby.

## Building LVC

Get the source code via 

	git clone https://github.com/sigurdschneider/lvc
	git submodule update --init --recursive

After installing the dependencies, you *can* (but if you did not change anthring, you do not have to) use

	./configure.sh

to generate `_CoqProject` from the sources. This step is strictly optional, as we also provide a `_CoqProject`
in this distribution. Then build LVC using

	make
	make extraction

This will generate a OCaml bytecode, and the following symbolic link will point to it

	extraction/lvcc.byte

There are some example files in extraction/examples. Run one by issuing the following command:

	cd extraction
	./lvcc.byte examples/dve.il
	./lvcc.byte examples/dve+dce.il

The output after different compilation phases will be in files `example/dve.il.$PHASE` where $PHASE is the 
compilation phase.

## Disclaimer

The sources incorporate ideas and code from various sources.

- The subdir `Containers` contains a copy of the [Containers library](http://www.lix.polytechnique.fr/coq/pylons/contribs/view/Containers/v8.4) which is available on [github](https://github.com/coq-contribs/containers/) was [slightly](https://github.com/sigurdschneider/containers) adapted for the needs of the project.
- The subdir `paco` contains a copy of the [Paco Library](http://plv.mpi-sws.org/paco/).
- The subdir TransVal/ contains work based on Heiko Becker's Bachelor's Thesis: [Verified SMT-based Translation Validation](http://compilers.cs.uni-saarland.de/publications/theses/becker_bsc.pdf).
- The file `Lattice.v` was inspired by the [Lattice development from Daniel W.H. James and Ralf Hinze](http://www.cs.ox.ac.uk/people/daniel.james/lattice.html).
- The file `Infra/SizeInduction.v` contains the type-class based size-induction from [AutoSubst](https://www.ps.uni-saarland.de/autosubst/).
- Parts of the spilling infrastructure in directory `Spilling` were done by [Julian Rosemann](https://www.ps.uni-saarland.de/~rosemann/bachelor.php) and published at ITP 2017[3].

## References

[1] Sigurd Schneider: Semantics of an Intermediate Language for Program Transformation. Master's Thesis. Saarland University, 2013.
[2] Sigurd Schneider, Gert Smolka, Sebastian Hack: A Linear First-Order Functional Intermediate Language for Verified Compilers. ITP 2015
[3] Julian Rosemann, Sigurd Schneider, Sebastian Hack: Verified Spilling and Translation Validation with Repair. ITP 2017
