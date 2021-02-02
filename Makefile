CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  Classes Relations IndType #Sets

INCLUDE_DEMO = -Q . CommonKnowledge
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -Q $(CURRENT_DIR) CommonKnowledge
DEP_FLAG = $(DEP_DEMO)

Classes_FILES = \
  RelationConstructorClasses.v AbstractEqual.v # AbstractOrder.v OrderClasses.v SetoidOrderClasses.v Bound.v Equivalence.v Predicate.v RelationClasses.v

Relations_FILES = \
  Mappings.v SetoidMappings.v Countable.v SetoidCountable.v RelationConstructors.v \
  IndCountable.v IndCountable_AuxDefs.v CountableExamples.v

#Fixpoint_FILES = \
#  CPO.v

#Sets_FILES = \
#  Ensemble.v SetoidEnsemble.v

IndType_FILES = \
  Syntax.v

FILES = \
  $(Classes_FILES:%.v=Classes/%.v) \
  $(IndType_FILES:%.v=IndType/%.v) \
  $(Relations_FILES:%.v=Relations/%.v) #\
#  $(Fixpoint_FILES:%.v=Fixpoint/%.v) \
#  $(Sets_FILES:%.v=Sets/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo)

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob

.DEFAULT_GOAL := all

include .depend

