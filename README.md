This is the development for the Bachelor's Thesis of

Heiko Becker
2537100

with the title: Verified Translation Validation in the LVC Framework

The development contains the LVC Compiler Project developed by Sigurd Schneider.
Dependencies can be found below.

The actual development done by Heiko Becker is in the folder TransVal.
The commit history stored in the .git folder documents the development process.

To build the Translation Validation Interface, the makefile must be generated
as explained below by Sigurd Schneider.

The interface can then be compiled with

    make TransVal/transval.v


Below is the original content of the README file from Sigurd Schneider that 
explains the necessary steps to build the full LVC project.

###############################################################################
#			Original README.md of Schneider			      #
###############################################################################

# LVC Compiler Project
IL - IL/I, IL/F and Coherence

Translation validation for register assignment and SSA construction

This is an advancement of http://www.ps.uni-saarland.de/~sdschn/master


## Dependencies

- **Coq**

    Sources compile with Coq version 8.4pl4 (May 2014).

- **Coq Containers Plugin**

    You need to have the containers library installed:
    http://coq.inria.fr/pylons/contribs/view/Containers/v8.4

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
