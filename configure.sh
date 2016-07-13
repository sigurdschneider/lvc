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
	echo "Ruby 1.9 not in path, defaulting to vanilla"
	VANILLA=yes
fi

BLACKLIST=`cat _BLACKLIST`
SOURCES=$(find theories -name \*.v -print | grep -v /\.# | grep -v $BLACKLIST | sed -e 's%^\./%%g')
coq_makefile -R . Lvc -R ContainersPlugin/theories Containers -I ContainersPlugin/src extraction $SOURCES > ${MAKEFILE}
echo "${MAKEFILE} generated."

echo "Patching ${MAKEFILE} to include target 'extraction'."
# sed -i -e  '/.\/extraction:/c\.\/extraction: Compiler.vo' Makefile
sed -i -e  's%\./extraction:%\./extraction: Compiler.vo%' ${MAKEFILE}

echo "Patching ${MAKEFILE} to reference external Containers documentation."
sed -i -e 's%COQDOCFLAGS?=-interpolate -utf8%COQDOCFLAGS?=--interpolate --utf8 --external "http://www.lix.polytechnique.fr/coq/pylons/contribs/files/Containers/v8.4/" Containers --toc --toc-depth 3 --index indexpage --no-lib-name%' ${MAKEFILE}


if [ -z "$VANILLA" ]; then
	echo "Patching ${MAKEFILE} to use ruby-based timing scripts (use --vanilla if undesired)."
	#sed -i -e 's/$(COQC) $(COQDEBUG) $(COQFLAGS)/@.\/time.sh $(if $(findstring j,$(MAKEFLAGS)),--parallel,) $(COQC) $(COQDEBUG) $(COQFLAGS)/' Makefile
	#sed -i -e 's/^TIMED=/TIMED=true/' Makefile
	sed -i -e 's/TIMECMD=/TIMECMD=@.\/time.rb $(if $(findstring j,$(MAKEFLAGS)),--parallel,)/' ${MAKEFILE}
fi
