##############################################################################
##                 The Calculus of Inductive Constructions                  ##
##                                                                          ##
##                                Projet Coq                                ##
##                                                                          ##
##                     INRIA                        ENS-CNRS                ##
##              Rocquencourt                        Lyon                    ##
##                                                                          ##
##                                  Coq V7                                  ##
##                                                                          ##
##                                                                          ##
##############################################################################

# WARNING
#
# This Makefile has been automagically generated by coq_makefile
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile chap9.v extract.v fib_intro1.v fib_ind.v fib_tail.v moreperms.v quadruple.v sig_rec_simple.v plus_prim.v exo_eqdec.v div3.v mod2.v div2_mod2.v plusss.v div3tofib_ind.v fib_positive.v sqrt.v 
#

##########################
#                        #
# Variables definitions. #
#                        #
##########################

CAMLP4LIB=`camlp4 -where`
COQSRC=-I $(COQTOP)/kernel -I $(COQTOP)/lib \
  -I $(COQTOP)/library -I $(COQTOP)/parsing \
  -I $(COQTOP)/pretyping -I $(COQTOP)/interp \
  -I $(COQTOP)/proofs -I $(COQTOP)/syntax -I $(COQTOP)/tactics \
  -I $(COQTOP)/toplevel -I $(COQTOP)/contrib/correctness \
  -I $(COQTOP)/contrib/extraction -I $(COQTOP)/contrib/field \
  -I $(COQTOP)/contrib/fourier -I $(COQTOP)/contrib/graphs \
  -I $(COQTOP)/contrib/interface -I $(COQTOP)/contrib/jprover \
  -I $(COQTOP)/contrib/omega -I $(COQTOP)/contrib/romega \
  -I $(COQTOP)/contrib/ring -I $(COQTOP)/contrib/xml \
  -I $(CAMLP4LIB)
ZFLAGS=$(OCAMLLIBS) $(COQSRC)
OPT=
COQFLAGS=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQC=$(COQBIN)coqc
GALLINA=gallina
COQDOC=coqdoc
CAMLC=ocamlc -c
CAMLOPTC=ocamlopt -c
CAMLLINK=ocamlc
CAMLOPTLINK=ocamlopt
COQDEP=$(COQBIN)coqdep -c
COQVO2XML=coq_vo2xml
GRAMMARS=grammar.cma
CAMLP4EXTEND=pa_extend.cmo pa_ifdef.cmo q_MLast.cmo
PP=-pp "camlp4o -I . -I $(COQTOP)/parsing $(CAMLP4EXTEND) $(GRAMMARS) -impl"

#########################
#                       #
# Libraries definition. #
#                       #
#########################

OCAMLLIBS=-I .
COQLIBS=-I .

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES=chap9.v\
  extract.v\
  fib_intro1.v\
  fib_ind.v\
  fib_tail.v\
  moreperms.v\
  quadruple.v\
  sig_rec_simple.v\
  plus_prim.v\
  exo_eqdec.v\
  div3.v\
  mod2.v\
  div2_mod2.v\
  plusss.v\
  div3tofib_ind.v\
  fib_positive.v\
  sqrt.v
VOFILES=$(VFILES:.v=.vo)
VIFILES=$(VFILES:.v=.vi)
GFILES=$(VFILES:.v=.g)
HTMLFILES=$(VFILES:.v=.html)
GHTMLFILES=$(VFILES:.v=.g.html)

all: chap9.vo\
  extract.vo\
  fib_intro1.vo\
  fib_ind.vo\
  fib_tail.vo\
  moreperms.vo\
  quadruple.vo\
  sig_rec_simple.vo\
  plus_prim.vo\
  exo_eqdec.vo\
  div3.vo\
  mod2.vo\
  div2_mod2.vo\
  plusss.vo\
  div3tofib_ind.vo\
  fib_positive.vo\
  sqrt.vo

spec: $(VIFILES)

gallina: $(GFILES)

html: $(HTMLFILES)

gallinahtml: $(GHTMLFILES)

all.ps: $(VFILES)
	$(COQDOC) -ps -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -ps -g -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

xml:: .xml_time_stamp
.xml_time_stamp: chap9.vo\
  extract.vo\
  fib_intro1.vo\
  fib_ind.vo\
  fib_tail.vo\
  moreperms.vo\
  quadruple.vo\
  sig_rec_simple.vo\
  plus_prim.vo\
  exo_eqdec.vo\
  div3.vo\
  mod2.vo\
  div2_mod2.vo\
  plusss.vo\
  div3tofib_ind.vo\
  fib_positive.vo\
  sqrt.vo
	$(COQVO2XML) $(COQFLAGS) $(?:%.o=%)
	touch .xml_time_stamp

####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend xml

.SUFFIXES: .v .vo .vi .g .html .tex .g.tex .g.html

.v.vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

.v.vi:
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

.v.g:
	$(GALLINA) $<

.v.tex:
	$(COQDOC) -latex $< -o $@

.v.html:
	$(COQDOC) -html $< -o $@

.v.g.tex:
	$(COQDOC) -latex -g $< -o $@

.v.g.html:
	$(COQDOC) -html -g $< -o $@

byte:
	$(MAKE) all "OPT="

opt:
	$(MAKE) all "OPT=-opt"

include .depend

.depend depend:
	rm -f .depend
	$(COQDEP) -i $(COQLIBS) *.v *.ml *.mli >.depend
	$(COQDEP) $(COQLIBS) -suffix .html *.v >>.depend

xml::

install:
	mkdir -p `$(COQC) -where`/user-contrib
	cp -f *.vo `$(COQC) -where`/user-contrib

clean:
	rm -f *.cmo *.cmi *.cmx *.o *.vo *.vi *.g *~
	rm -f all.ps all-gal.ps $(HTMLFILES) $(GHTMLFILES)

archclean:
	rm -f *.cmx *.o

# WARNING
#
# This Makefile has been automagically generated by coq_makefile
# Edit at your own risks !
#
# END OF WARNING

