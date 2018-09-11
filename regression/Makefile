OCAMLC = ocamlfind c
OCAMLOPT = ocamlfind opt
OCAMLDEP = ocamlfind dep
SOURCES = common.ml $(TOPFILE).ml
CAMLP5 = -syntax camlp5o -package ostap.syntax,GT.syntax.all
PXFLAGS = $(CAMLP5)
BFLAGS = -rectypes -I ../src
OFLAGS = $(BFLAGS)

all: .depend $(TOPFILE).opt

.depend: $(SOURCES)
	$(OCAMLDEP) $(PXFLAGS) *.ml > .depend

$(TOPFILE).opt: $(SOURCES:.ml=.cmx)
	$(OCAMLOPT) -o $(TOPFILE).opt $(OFLAGS) $(LIBS:.cma=.cmxa) -linkpkg -package ostap Syntax.cmx SM.cmx Embedding.cmx $(SOURCES:.ml=.cmx)

$(TOPFILE).byte: $(SOURCES:.ml=.cmo)
	$(OCAMLC) -o $(TOPFILE).byte $(BFLAGS) $(LIBS) -linkpkg -package ostap Syntax.cmo SM.cmo Embedding.cmo $(SOURCES:.ml=.cmo) 

clean:
	rm -Rf *.cmi *.cmo *.cmx *.annot *.o *.opt *.byte *~ .depend *.log

-include .depend
# generic rules

###############
%.cmi: %.mli
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

# Note: cmi <- mli should go first
%.cmi: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.cmo: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.o: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

