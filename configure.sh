#!/bin/bash

function display_help {
  echo "configure.sh - Generate a Coq Makefile for this directory"
  echo ""
  echo -e "  --help\t Show this text"
  echo -e "  --vanilla\t Do not patch makefile to use ruby-based timing scripts"
}

VANILLA=

while [ $# != 0 ]; do
  case "$1" in
  --help)  display_help;;
  --vanilla) VANILLA=yes;;
  *)         
  esac
  shift
done


SOURCES=`find -type f -iname '*.v' -printf '%P\n'`
coq_makefile -R . Lvc extraction $SOURCES > Makefile
echo "Makefile generated."

if [ -z "$VANILLA" ]; then
	echo "Patching Makefile to use ruby-based timing scripts (use --vanilla if undesired)."
  sed -i '/.\/extraction:/c\.\/extraction: Compiler.vo' Makefile
  sed -i 's/$(COQC) $(COQDEBUG) $(COQFLAGS)/@.\/time.sh $(if $(findstring j,$(MAKEFLAGS)),--parallel,) $(COQC) $(COQDEBUG) $(COQFLAGS)/' Makefile
fi


