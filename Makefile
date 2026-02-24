.PHONY: default docker-build run integration-test unit-test tests checks tags TAGS

default: tests

# Build container.
docker-build:
	docker -l warn build --build-arg USER_ID=$(id -u) \
             --build-arg GROUP_ID=$(id -g) \
             --progress=plain \
             -t cbmc:latest .

# Run the container.
run:
	@bash run.sh

# Run unit tests with `pytest` within container.
unit-test:
	bash run.sh pytest --ignore=test/integration

# Run integration tests with `pytest` within container.
integration-test:
	bash run.sh pytest test/integration

# Run all tests
tests: unit-test integration-test

# Run all code style checks.
checks: style-fix style-check

# Code style; defines `style-check` and `style-fix`.
# TODO: I'm not sure why `style.yml` and `test.yml` GitHub workflow actions don't verify.
CODE_STYLE_EXCLUSIONS_USER := --exclude-dir cbmc --exclude-dir test --exclude __init__.py
ifeq (,$(wildcard .plume-scripts))
dummy := $(shell git clone --depth=1 -q https://github.com/plume-lib/plume-scripts.git .plume-scripts)
endif
include .plume-scripts/code-style.mak

# ${PYTHON_FILES} is defined by the above style checking.
TAGS: tags
tags:
	etags ${PYTHON_FILES}
