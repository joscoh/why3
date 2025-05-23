
BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../bin/why3.opt
  WHY3SHARE=../../share
else
  ifeq ($(BINDIR),)
    WHY3=why3
  else
    WHY3=$(BINDIR)/why3
  endif
  WHY3SHARE=$(shell $(WHY3) --print-datadir)
endif

include $(WHY3SHARE)/Makefile.config

ifeq ($(BENCH),yes)
  INCLUDE += -I ../../lib/why3
endif

MAIN=main
GEN =sudoku
OBJ=$(GEN)

GENML = $(addsuffix .ml, $(GEN))
ML = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

extract: $(GENML)

doc:
	$(WHY3) doc ../sudoku.mlw
	$(WHY3) session html .

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(INCLUDE) zarith.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) zarith.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(GENML): ../sudoku.mlw
	$(WHY3) extract -D ocaml64 --recursive -o $@ -L .. sudoku.Test

# javascript


JSMAIN=jsmain

JSOCAMLC=ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml-ppx -package js_of_ocaml-lwt

$(JSMAIN).js: $(JSMAIN).byte
	js_of_ocaml +nat.js $(JSMAIN).byte

$(JSMAIN).byte: $(CMO) $(JSMAIN).cmo
	$(JSOCAMLC) $(INCLUDE) zarith.cma -o $@ -linkpkg $^

%.cmo: %.ml
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

%.cmi: %.mli
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

clean::
	rm -f $(GENML) *.annot *.o *.cm[xio] $(MAIN).opt $(MAIN).byte
	rm -f sudoku__*.ml why3__*.ml
	rm -f int__Int.ml map__Map.ml array__Array.ml
