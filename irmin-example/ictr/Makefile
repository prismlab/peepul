include Makefile.include

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: out library ictr output

ictr: ictr.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Ictr' ictr.fst --record_hints

library: library.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Library' library.fst --record_hints

output: library ictr
	cd out; $(OCAMLOPT) -package zarith,irmin-unix  Library.ml Ictr.ml

out:
	mkdir -p out

clean:
	rm -rf out *~ *.exe
