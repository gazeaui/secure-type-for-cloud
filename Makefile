
ML = ast.ml parser.ml lexer.ml  printers.ml typechecker.ml reductions.ml  parser_operations.ml lexer_operations.ml main.ml 
MLI = $(wildcard $(ML:.ml=.mli)) parser.mli parser_operations.mli
OCAMLC = ocamlfind ocamlopt -g -annot -package str,unix
OCAMLDEP = ocamldep -native
CMA = cmxa
CMO = cmx
OBJS = $(ML:.ml=.$(CMO))

types: $(OBJS)
	$(OCAMLC) -linkpkg -o types $(OBJS)



%.$(CMO): %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

%.ml: %.mly
	ocamlyacc $<

%.ml: %.mll
	ocamllex $<

.depend: $(ML) $(MLI)
	$(OCAMLDEP) $(ML) $(MLI) > .depend

-include .depend

clean::
	rm -f *.o *.cmi *.cmx *.cmo *.annot
	rm -f types
	rm -f .depend

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc




