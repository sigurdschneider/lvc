DOC := doc/
DOCIND := doc-ind/
DOCSPILL := doc-spill/
PKGIND := pkg-lvc-ind/
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
VS=$(shell find theories/ -iname '*.v' | grep -v '/\.')
VSIND=$(shell find theories/ -iname '*vo' | sed 's/\.vo/.v/' | grep -v 'Spilling' | grep -v 'ValueOpts' | grep -v 'TransVal')
VSSPILL=$(shell find theories/ -iname '*vo' | sed 's/\.vo/.v/' | grep -v 'ValueOpts' | grep -v 'TransVal')
DOCS=$(shell find extra/ )
COMPCERTCFG=ppc-linux

ifeq ($(wildcard time.rb)$(wildcard .timing),time.rb.timing)
  export TIMECMD=@./time.rb $(if $(findstring j,$(MAKEFLAGS)),--parallel,)
endif
export COQDOCFLAGS=--interpolate --utf8 --toc --toc-depth 3 --index indexpage --no-lib-name
export VERBOSE=false

#if [[ -z "$VANILLA" && -e "time.rb" ]]; then \
#	echo "Patching ${MAKEFILE} to use ruby-based timing scripts (use --vanilla if undesired)."

ifneq "$(COQBIN)" ""
        COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE) dep
	+$(MAKE) -f $(COQMAKEFILE) $@

depmakefiles:
	+$(MAKE) -C paco Makefile.coq
	+$(MAKE) -C ContainersPlugin Makefile.coq

CompCert/Makefile.config: 
	cd CompCert && ./configure $(COMPCERTCFG) 

compcert: CompCert/Makefile.config
	-+$(MAKE) -C CompCert 

dep: compcert
	+$(MAKE) -C paco all TIMECMD=
	+$(MAKE) -C ContainersPlugin all TIMECMD=
	+$(MAKE) -C smpl all TIMECMD=

depclean: clean
	+$(MAKE) -C paco clean
	+$(MAKE) -C ContainersPlugin clean
	+$(MAKE) -C compiler clean
	+$(MAKE) -C smpl clean
	rm -rf compiler/extraction/*

distclean: clean depclean
	find $(PKGIND)/ -type f -iname '*.vo' -o -iname '*.glob' -o -iname '*.v.d' | xargs rm -rf

doc: clean-doc $(DOCS) dep $(COQMAKEFILE)
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

doc-ind-publish: doc-ind ind-package
	scp -r $(DOCIND)/* ps:public_html/lvc-ind/
	#scp -r lvc-ind.tgz ps:public_html/lvc-ind/

ind-package:
	rm -rf $(PKGIND)
	mkdir $(PKGIND)
	cp -r _CoqProject compiler ContainersPlugin extra Makefile configure.sh paco src theories README.md $(PKGIND)
	find $(PKGIND)/ -type f -iname '*.vo' -o -iname '*.glob' -o -iname '*.v.d' -o -iname '*.time' -o -iname '*.aux' | xargs rm -rf
	rm -rf $(PKGIND)/theories/Spilling $(PKGIND)/theories/TransVal $(PKGIND)/theories/ValueOpts $(PKGIND)/theories/Test*
	$(MAKE) -C $(PKGIND) clean depclean
	cp Make Makefile.coq $(PKGIND)
	rm -rf $(PKGIND)/src/*.cm* $(PKGIND)/src/*.o $(PKGIND)/src/*.ml4.d
	rm -rf $(PKGIND)/compiler/lvcc.native
	tar cvzf lvc-ind.tgz $(PKGIND)

doc-spill: clean-doc $(DOCS)
	- mkdir -p $(DOCSPILL)
	make -f $(COQMAKEFILE) $(VSSPILL:.v=.vo) -j$(CORES)
	coqdoc $(COQDOCFLAGS) -d $(DOCSPILL) $(shell cat _CoqProject | grep -v ^-I) $(VSSPILL)
	find theories/ -iname '*vo' | sed 's/\.vo/.v/' | grep -v 'ValueOpts' | grep -v 'TransVal' | tar -cvzf $(DOCSPILL)/lvc-spill.tgz -T -
	cp $(EXTRA_DIR)/resources/* $(DOCSPILL)
	cp $(EXTRA_DIR)/index-spill.html $(DOCSPILL)/index.html
	cp $(EXTRA_DIR)/search-toc.html $(DOCSPILL)/search-toc.html

doc-spill-publish: doc-spill
	scp -r $(DOCSPILL)/* ps:public_html/lvc-spill/

clean-doc:
	rm -rf $(DOC)

clean: clean-doc
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

$(COQMAKEFILE): Makefile depmakefiles $(VS)
	$(COQBIN)coq_makefile -f Make -o Makefile.coq
	sed -i s/TIMECMD=/TIMECMD?=/ Makefile.coq
#	./configure.sh
#	coq_makefile -f _CoqProject $(VS) -o $(COQMAKEFILE)

Make: ;

extraction: theories/Compiler.vo compiler/extraction.v compiler/STAMP
	+$(MAKE) -C compiler all

compiler/STAMP: theories/Compiler.vo compiler/extraction.v
	mkdir -p compiler/extraction
	rm -f theories/extraction.vo
	rm -f compiler/extraction/*
	coqtop $(shell cat _CoqProject) -batch -load-vernac-source compiler/extraction.v
	touch compiler/STAMP

%.vo:: $(COQMAKEFILE)
	make -f $(COQMAKEFILE) -j$(CORES) $@

.PHONY: all clean clean-doc doc
