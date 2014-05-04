#!/bin/bash

SOURCES=`find -type f -iname '*.v' -printf '%P\n'`
coq_makefile -R . Lvc extraction $SOURCES > Makefile
sed -i '/.\/extraction:/c\.\/extraction: Compiler.vo' Makefile
sed -i 's/$(COQC) $(COQDEBUG) $(COQFLAGS)/@.\/time.sh $(if $(findstring j,$(MAKEFLAGS)),--parallel,) $(COQC) $(COQDEBUG) $(COQFLAGS)/' Makefile



