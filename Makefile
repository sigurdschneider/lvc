DOC := doc/
EXTRA_DIR := extra
HEADER := $(EXTRA_DIR)/header.html
FOOTER := $(EXTRA_DIR)/footer.html
COQDOCFLAGS := \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(HEADER) --with-footer $(FOOTER) \
  -d $(DOC)
COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)
CORES=$(shell cat /proc/cpuinfo | grep cpu\ cores | sed 's/.*:\ //' | head -n 1)
VS=$(shell find -iname '*vo' | sed 's/\.vo/.v/' | grep -v paco | grep -v Containers)

ifneq "$(COQBIN)" ""
        COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) $@

doc: clean-doc 
	- mkdir -p $(DOC)
	coqdoc $(COQDOCFLAGS) `cat _CoqProject` $(VS)
	cp $(EXTRA_DIR)/resources/* $(DOC)
#	make -f $(COQMAKEFILE) html COQDOCFLAGS="$(COQDOCFLAGS)"


clean-doc:
	rm -rf $(DOC)

clean: clean-doc
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

$(COQMAKEFILE): Makefile $(VS)
	./configure.sh
#	coq_makefile -f _CoqProject $(VS) -o $(COQMAKEFILE)

#%:: $(COQMAKEFILE)
#	make -f $(COQMAKEFILE) -j$(CORES) $@

.PHONY: all clean clean-doc doc
