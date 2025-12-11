.PHONY: default docker-build run test checks style-fix style-check python-style-fix python-style-check python-typecheck showvars

default: test

# Build container.
docker-build:
	docker -l warn build --build-arg USER_ID=$(id -u) \
             --build-arg GROUP_ID=$(id -g) \
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
# SH_SCRIPTS_USER := dots/.aliases dots/.environment dots/.profile
# BASH_SCRIPTS_USER := dots/.bashrc dots/.bash_profile
# CODE_STYLE_EXCLUSIONS_USER := --exclude-dir apheleia --exclude-dir 'apheleia-*' --exclude-dir=mew --exclude=csail-athena-tickets.bash --exclude=conda-initialize.sh --exclude=addrfilter 
ifeq (,$(wildcard .plume-scripts))
dummy != git clone -q https://github.com/plume-lib/plume-scripts.git .plume-scripts
endif
include .plume-scripts/code-style.mak

TAGS: tags
tags:
	etags ${PYTHON_FILES}
