all: Makefile.coq
	$(MAKE) -f Makefile.coq all

%.vo: %.v Makefile.coq
	$(MAKE) -f Makefile.coq $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
