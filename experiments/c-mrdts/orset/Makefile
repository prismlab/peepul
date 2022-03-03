include Makefile.include

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: orset

orset: out orset_bst.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Orset_bst' orset_bst.fst --record_hints

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
