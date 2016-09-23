#! /bin/bash

MAKEFILE=Makefile.coq
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

if ! [[ $(ruby -v) =~ ^ruby\ 2.1 ]]; then
	echo "Ruby not in path, defaulting to vanilla"
	VANILLA=yes
fi

BLACKLIST=`cat _BLACKLIST`
SOURCES=$(find theories -name \*.v -print | grep -v /\.# | grep -v $BLACKLIST | sed -e 's%^\./%%g')
coq_makefile $(cat _CoqProject) src/lvc_plugin.ml4 $SOURCES  > ${MAKEFILE}
echo "${MAKEFILE} generated."

echo "Patching ${MAKEFILE} to include custom COQDOCFLAGS."
sed -i -e 's%COQDOCFLAGS?=-interpolate -utf8%COQDOCFLAGS?=--interpolate --utf8 --toc --toc-depth 3 --index indexpage --no-lib-name%' ${MAKEFILE}


if [ -z "$VANILLA" ]; then
	echo "Patching ${MAKEFILE} to use ruby-based timing scripts (use --vanilla if undesired)."
	sed -i -e 's/TIMECMD=/TIMECMD=@.\/time.rb $(if $(findstring j,$(MAKEFLAGS)),--parallel,)/' ${MAKEFILE}
fi
