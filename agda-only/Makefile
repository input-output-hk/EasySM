MAKEFLAGS += --no-builtin-rules --no-builtin-variables

.SUFFIXES :

.PHONY : all clean deepclean

HTML := $(patsubst src/%.agda,docs/%.html,$(shell find src -type f -name '*.agda'))
AGDA := $(shell find src -type f -name '*.agda')

all : $(HTML)

docs/%.html : $(AGDA)
	agda -i src --html --html-dir=docs --html-highlight=auto $(patsubst docs/%.html,src/%.agda,$@)

clean :
	-rm -r docs

deepclean : clean
	find src -type f -name '*.agdai' -delete
