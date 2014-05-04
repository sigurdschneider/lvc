#!/bin/bash

SOURCES=`find -type f -iname '*.v' -printf '%P\n'`
coq_makefile -R . Lvc extraction $SOURCES > Makefile
sed -i '/.\/extraction:/c\.\/extraction: Compiler.vo' Makefile
sed -i 's/$(COQC) $(COQDEBUG) $(COQFLAGS)/@$(COQC) $(COQDEBUG) $(COQFLAGS)/' Makefile
sed -i '/COQCHK?=$(COQBIN)coqchk/a COQC:=./time.sh $(COQC)' Makefile



