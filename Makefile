TARGET     = main
TEST       = test
OPTS       = -use-ocamlfind
TAGS       = annot,debug
LIBS       = unix,str,graph,oUnit
PKGS       = batteries,ocamlgraph
EXTENSION  = byte
RUN_TEST   = ./$(TEST).$(EXTENSION)
CFLAGS     = -w A -w -4 -w -27 -short-paths
OCAMLBUILD = ocamlbuild $(OPTS) -tags $(TAGS) -pkgs $(PKGS) -cflags "$(CFLAGS)"

.PHONY: all clean

all:
	$(OCAMLBUILD) $(TARGET).$(EXTENSION)

clean:
	$(OCAMLBUILD) -clean
