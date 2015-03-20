#! /bin/sh

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

if ! [[ $(ruby -v) =~ ^ruby\ 1.9 ]]; then
	echo "Ruby 1.9 not in path, defaulting to vanilla"
	VANILLA=yes
fi

SOURCES=$(find . -name \*.v -print | grep -v /\.# | sed -e 's%^\./%%g')
coq_makefile -R . Lvc extraction $SOURCES > Makefile
echo "Makefile generated."

echo "Patching Makefile to include target 'extraction'."
# sed -i -e  '/.\/extraction:/c\.\/extraction: Compiler.vo' Makefile
sed -i -e  's%\./extraction:%\./extraction: Compiler.vo%' Makefile

echo "Patching Makefile to reference external Containers documentation."
sed -i -e 's%COQDOCFLAGS?=-interpolate -utf8%COQDOCFLAGS?=--interpolate --utf8 --external "http://www.lix.polytechnique.fr/coq/pylons/contribs/files/Containers/v8.4/" Containers --toc --toc-depth 3 --index indexpage --no-lib-name%' Makefile


if [ -z "$VANILLA" ]; then
	echo "Patching Makefile to use ruby-based timing scripts (use --vanilla if undesired)."
	sed -i -e 's/$(COQC) $(COQDEBUG) $(COQFLAGS)/@.\/time.sh $(if $(findstring j,$(MAKEFLAGS)),--parallel,) $(COQC) $(COQDEBUG) $(COQFLAGS)/' Makefile
fi
