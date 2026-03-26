SOURCE      := $(shell find src -type f -iname '*.odin')
SOURCE_CLIE := $(shell find cli -type f -iname '*.odin')

FLAGS := \
	-terse-errors \
	-error-pos-style:unix \
	-strict-style \
	-vet-tabs \
	-vet-unused \
	-vet-unused-variables \
	-vet-unused-imports \
	-vet-using-stmt

.PHONY: all

all: build build/uxnsmal
	@echo "DONE!"

build:
	mkdir -p build

build/uxnsmal: $(SOURCE) $(SOURCE_CLIE)
	@echo "INFO: Compiling UXNSMAL..."
	@odin build cli -out:build/uxnsmal -debug $(FLAGS)

fmt:
	@odinfmt src -w > /dev/null
	@odinfmt cli -w > /dev/null
