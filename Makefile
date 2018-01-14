GDOC := doc/
DOC := doc-all/
CONTAINERSDOC := doc-cont/
DOCIND := doc-ind/
DOCSPILL := doc-spill/
PKGIND := pkg-lvc-ind/
PKGSPILL := pkg-lvc-spill/
EXTRA_DIR := extra
HEADER := $(EXTRA_DIR)/header.html
FOOTER := $(EXTRA_DIR)/footer.html
COQDOCFLAGSX := \
	--external 'https://www.ps.uni-saarland.de/~sdschn/LVC/doc-cont' Containers \
  --toc --utf8 --toc-depth 3 --html --interpolate \
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
	-cd CompCert && ./configure $(COMPCERTCFG) -ignore-coq-version

compcert: CompCert/Makefile.config
	-+$(MAKE) -C CompCert extraction driver/Version.ml

dep: compcert
	+$(MAKE) -C paco all TIMECMD=
	+$(MAKE) -C ContainersPlugin all TIMECMD=
	+$(MAKE) -C smpl all TIMECMD=

depclean: clean
	+$(MAKE) -C paco clean
	+$(MAKE) -C ContainersPlugin clean
	+$(MAKE) -C compiler clean
	+$(MAKE) -C smpl clean
	+$(MAKE) -C CompCert clean distclean
	rm -rf compiler/extraction/*

distclean: clean depclean
	find $(PKGIND)/ -type f -iname '*.vo' -o -iname '*.glob' -o -iname '*.v.d' | xargs rm -rf

doc: clean-doc $(DOCS) dep $(COQMAKEFILE)
	- mkdir -p $(DOC)
	make -f $(COQMAKEFILE) -j$(CORES) -k
	coqdoc $(COQDOCFLAGSX) -d $(DOC) $(shell cat _CoqProject | grep -v ^-I | grep -v mlpack | grep -v ml4)
	cp $(EXTRA_DIR)/resources/* $(DOC)
	cp $(EXTRA_DIR)/index-all.html $(DOC)/index.html
	cp $(EXTRA_DIR)/search-toc.html $(DOC)/search-toc.html

doc-publish: doc
	scp -r $(DOC)/* ps:public_html/LVC/doc-all/
	make -C ContainersPlugin doc
	scp -r ContainersPlugin/html/* ps:public_html/LVC/doc-cont/

doc-quick: 
	scp -r $(DOC)/* ps:public_html/LVC/doc-all/

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

spill-package:
	rm -rf $(PKGSPILL)
	mkdir $(PKGSPILL)
	cp -r _CoqProject compiler ContainersPlugin smpl extra Makefile configure.sh paco src theories README.md CompCert $(PKGSPILL)
	touch $(PKGSPILL)/_blacklist
	find $(PKGSPILL)/ -type f -iname '*.vo' -o -iname '*.glob' -o -iname '*.v.d' -o -iname '*.time' -o -iname '*.aux' | xargs rm -rf
	rm -rf $(PKGSPILL)/theories/TransVal $(PKGSPILL)/theories/ValueOpts $(PKGSPILL)/theories/Test* $(PKGSPILL)/theories/Lowering/ToMach.v $(PKGSPILL)/theories/DCE.v
	$(MAKE) -C $(PKGSPILL) clean depclean
	cp Makefile.coq $(PKGSPILL)
	rm -rf $(PKGSPILL)/src/*.cm* $(PKGSPILL)/src/*.o $(PKGSPILL)/src/*.ml4.d
	rm -rf $(PKGSPILL)/compiler/lvcc.native
	cd $(PKGSPILL); ./configure.sh
	tar cvzf lvc-spill.tgz $(PKGSPILL)

doc-spill: clean-doc $(DOCS)
	- mkdir -p $(DOCSPILL)
	make -f $(COQMAKEFILE) $(VSSPILL:.v=.vo) -j$(CORES)
	coqdoc $(COQDOCFLAGS) -d $(DOCSPILL) $(shell cat _CoqProject | grep -v ^-I) $(VSSPILL)
	cp $(EXTRA_DIR)/resources/* $(DOCSPILL)
	cp $(EXTRA_DIR)/index-spill.html $(DOCSPILL)/index.html
	cp $(EXTRA_DIR)/search-toc.html $(DOCSPILL)/search-toc.html

doc-spill-publish: doc-spill spill-package
	cp lvc-spill.tgz $(DOCSPILL)/
	-ssh ps rm public_html/lvc-spill/*
	scp -r $(DOCSPILL)/* ps:public_html/lvc-spill/
	ssh ps chmod -R g+w public_html/lvc-spill
	ssh ps chown -R :gosarights public_html/lvc-spill

clean-doc:
	rm -rf $(DOC)

clean: clean-doc
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

$(COQMAKEFILE): Makefile depmakefiles $(VS)
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
#	./configure.sh
#	coq_makefile -f _CoqProject $(VS) -o $(COQMAKEFILE)

Make: ;

extraction: compiler/STAMP
	+$(MAKE) -C compiler all

compiler/STAMP: theories/Compiler.vo compiler/extraction.v theories/Lowering/ToLinear.vo theories/Lowering/LinearToAsm.vo theories/Lowering/IsLinearizable.vo
	mkdir -p compiler/extraction
	rm -f compiler/extraction/*
	coqtop $(shell cat Make) -batch -load-vernac-source compiler/extraction.v
	touch compiler/STAMP

%.vo:: $(COQMAKEFILE)
	make -f $(COQMAKEFILE) -j$(CORES) $@

.PHONY: all clean clean-doc doc
