include Makefile.include

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: pnctr

pnctr: out pnctr.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Pnctr' pnctr.fst --record_hints

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
