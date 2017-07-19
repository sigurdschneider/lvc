#! /bin/bash

function display_help {
  echo "configure.sh - Generate a file 'Make' which can be used to"
	echo "               generate Makefile.coq for this directory"
  echo ""
  echo -e "  --help\t Show this text"
  echo -e "  --timing\t Use timing scripts"
}

TIMING=
while [ $# != 0 ]; do
  case "$1" in
  --help)  display_help;;
  --timing) TIMING=yes;;
  *)
  esac
  shift
done

if ! [[ $(ruby -v) =~ ^ruby\ 2.2 ]]; then
	echo "Ruby 2.2 not in path, disabling timing"
	TIMING=no
fi

if [[ "$TIMING" = "yes" ]]; then
	echo "Created .timing to indicate usage of timing script"
	touch .timing
fi

coq_ver=$(${COQBIN}coqc -v 2>/dev/null | sed -n -e 's/The Coq Proof Assistant, version \([^ ]*\).*$/\1/p')
case "$coq_ver" in
  8.6*)
		;;
  8.7*)
    echo "Warning: LVC does not compile with Coq 8.7 yet, you are on your own."
		;;
	*)
    echo "Error: Need Coq 8.6"
		exit 1
esac
echo "Found Coq version $coq_ver."

SOURCES=$(find theories -name \*.v -print | grep -v /\.# | sed -e 's%^\./%%g' | sort)
RM=$(for pat in $(cat _blacklist); do echo "$SOURCES" | grep -e $pat ; done | sort)
FILTERSOURCES=$(comm -23 <(echo "$SOURCES") <(echo "$RM"))
echo "Removed due to blacklist:"
echo "$RM"
cat _CoqProject > Make
echo >> Make
echo "src/lvc_plugin.mlpack" >> Make
echo "src/lvc_tacs.ml4" >> Make
echo >> Make
echo $FILTERSOURCES  >> Make
echo "Make generated."
