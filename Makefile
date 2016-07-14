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
VS=$(shell find theories/ -iname '*vo' | sed 's/\.vo/.v/' | grep -v `cat _BLACKLIST`)

ifneq "$(COQBIN)" ""
        COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE) dep
	+$(MAKE) -f $(COQMAKEFILE) $@

depmakefiles:
	+$(MAKE) -C paco Makefile.coq
	+$(MAKE) -C ContainersPlugin Makefile.coq

dep:
	+$(MAKE) -C paco all
	+$(MAKE) -C ContainersPlugin all

depclean: clean
	+$(MAKE) -C paco clean
	+$(MAKE) -C ContainersPlugin clean

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

$(COQMAKEFILE): Makefile depmakefiles $(VS)
	./configure.sh
#	coq_makefile -f _CoqProject $(VS) -o $(COQMAKEFILE)

#%:: $(COQMAKEFILE)
#	make -f $(COQMAKEFILE) -j$(CORES) $@

.PHONY: all clean clean-doc doc
