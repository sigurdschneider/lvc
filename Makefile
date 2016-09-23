DOC := doc/
DOCIND := doc-ind/
PKGIND := pkg-ind/
EXTRA_DIR := extra
HEADER := $(EXTRA_DIR)/header.html
FOOTER := $(EXTRA_DIR)/footer.html
COQDOCFLAGS := \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(HEADER) --with-footer $(FOOTER)
COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)
CORES=$(shell cat /proc/cpuinfo | grep cpu\ cores | sed 's/.*:\ //' | head -n 1)
VS=$(shell find theories/ -iname '*.v' | grep -v '/\.' | grep -v `cat _BLACKLIST`)
VSIND=$(shell find theories/ -iname '*vo' | sed 's/\.vo/.v/' | grep -v `cat _BLACKLIST` | grep -v 'Spilling')
DOCS=$(shell find extra/ )

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

doc: clean-doc $(DOCS)
	- mkdir -p $(DOC)
	-make -f $(COQMAKEFILE) -j$(CORES) -k
	coqdoc $(COQDOCFLAGS) -d $(DOC) $(shell cat _CoqProject | grep -v ^-I) $(shell find theories/ -iname '*.vo' | sed 's/\.vo/.v/')
	cp $(EXTRA_DIR)/resources/* $(DOC)
	cp $(EXTRA_DIR)/index.html $(DOC)/index.html
	cp $(EXTRA_DIR)/search-toc.html $(DOC)/search-toc.html

doc-publish: doc
	scp -r $(DOC) ps:public_html/LVC

doc-ind: clean-doc $(DOCS)
	- mkdir -p $(DOCIND)
	make -f $(COQMAKEFILE) $(VSIND:.v=.vo) -j$(CORES)
	coqdoc $(COQDOCFLAGS) -d $(DOCIND) $(shell cat _CoqProject | grep -v ^-I) $(VSIND)
	cp $(EXTRA_DIR)/resources/* $(DOCIND)
	cp $(EXTRA_DIR)/index-ind.html $(DOCIND)/index.html
	cp $(EXTRA_DIR)/search-toc.html $(DOCIND)/search-toc.html

doc-ind-publish: doc-ind
	scp -r $(DOCIND)/* ps:public_html/lvc-ind/

ind-package:
	rm -rf $(PKGIND)
	mkdir $(PKGIND)
	cp -r compiler ContainersPlugin extra Makefile configure.sh paco src theories $(PKGIND)
	find $(PKGIND)/ -type f -iname '*.vo' -o -iname '*.glob' -o -iname '*.v.d' -o -iname '*.time' | xargs rm -rf 
	rm -rf $(PKGIND)/theories/Spilling $(PKGIND)/theories/TransVal
	rm -rf $(PKGIND)/theories/Spilling $(PKGIND)/theories/TransVal $(PKGIND)/ValueOpts/
	$(MAKE) -C $(PKGIND) clean depclean

clean-doc:
	rm -rf $(DOC)

clean: clean-doc
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

$(COQMAKEFILE): Makefile depmakefiles $(VS)
	./configure.sh
#	coq_makefile -f _CoqProject $(VS) -o $(COQMAKEFILE)


extraction: compiler/STAMP compiler/extraction.v theories/Compiler.vo
	+$(MAKE) -C compiler

compiler/STAMP: theories/Compiler.vo compiler/extraction.v
	rm -f theories/extraction.vo
	rm -f compiler/extraction/*
	coqtop $(shell cat _CoqProject) -batch -load-vernac-source compiler/extraction.v
	touch compiler/STAMP

%.vo:: $(COQMAKEFILE)
	make -f $(COQMAKEFILE) -j$(CORES) $@

.PHONY: all clean clean-doc doc
