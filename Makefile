.PHONY: default docker-build run test checks tags TAGS

default: test

# Build container.
docker-build:
	docker -l warn build --build-arg USER_ID=$(id -u) \
             --build-arg GROUP_ID=$(id -g) \
             --progress=plain \
             -t cbmc:latest .

# Run the container.
run:
	@bash run.sh

# Run `pytest` within container.
test:
	bash run.sh pytest

# Run all code style checks.
checks: style-fix style-check

# Code style; defines `style-check` and `style-fix`.
CODE_STYLE_EXCLUSIONS_USER := --exclude-dir cbmc --exclude-dir test --exclude __init__.py
ifeq (,$(wildcard .plume-scripts))
dummy != git clone -q https://github.com/plume-lib/plume-scripts.git .plume-scripts
endif
include .plume-scripts/code-style.mak

# ${PYTHON_FILES} is defined by the above style checking.
TAGS: tags
tags:
	etags ${PYTHON_FILES}
