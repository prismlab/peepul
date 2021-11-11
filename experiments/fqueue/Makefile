include Makefile.include

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: fqueue

fqueue: out fqueue.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Fqueue' fqueue.fst --record_hints

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
