ROCQ ?= rocq
PROJECT := _CoqProject

SOURCES := $(wildcard *.v)
OBJECTS := $(SOURCES:.v=.vo)
DEPS := .Makefile.deps

# Proof General reads the same load paths from _CoqProject.
COQPATH := $(shell sed -n '/^-Q /p' $(PROJECT))
COQFLAGS := -q -native-compiler no $(COQPATH)

.PHONY: all clean
all: $(OBJECTS)

$(OBJECTS): %.vo: %.v Makefile $(PROJECT)
	$(ROCQ) compile $(COQFLAGS) $<

$(DEPS): $(SOURCES) Makefile $(PROJECT)
	$(ROCQ) dep -f $(PROJECT) $(SOURCES) > $@

ifneq ($(filter clean,$(MAKECMDGOALS)),clean)
-include $(DEPS)
endif

clean:
	rm -f $(OBJECTS) $(SOURCES:.v=.glob) $(SOURCES:.v=.vos) \
	      $(SOURCES:.v=.vok) $(SOURCES:.v=.v.beautified) \
	      $(SOURCES:.v=.required_vo) $(addprefix .,$(SOURCES:.v=.aux)) $(DEPS)
