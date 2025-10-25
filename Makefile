.PHONY: docker-build test style-fix style-check python-style-fix python-style-check python-typecheck showvars

# Build container.
docker-build:
	docker build --build-arg USER_ID=$(id -u) \
             --build-arg GROUP_ID=$(id -g) \
             -t cbmc:latest .

# Run `pytest` within container.
test:
	bash run.sh pytest

# Code style.
style-fix: python-style-fix
style-check: python-style-check python-typecheck
PYTHON_FILES:=$(shell find . \( -name ".git" -o -name ".venv" -o -name "test" \) -prune -o -name '*.py' -not -name '__init__.py' -print) $(shell grep -r -l --exclude-dir=.git --exclude-dir=.venv --exclude='*.py' --exclude='*~' --exclude='*.tar' --exclude-dir=test --exclude=gradlew --exclude=lcb_runner '^\#! \?\(/bin/\|/usr/bin/env \)python')
python-style-fix:
ifneq (${PYTHON_FILES},)
	@ruff --version
	@ruff format ${PYTHON_FILES}
	@ruff -q check ${PYTHON_FILES} --fix
endif
python-style-check:
ifneq (${PYTHON_FILES},)
	@ruff --version
	@ruff -q format --check ${PYTHON_FILES}
	@ruff -q check ${PYTHON_FILES}
endif
python-typecheck:
ifneq (${PYTHON_FILES},)
	@mypy --version
	@mypy --strict --install-types --non-interactive ${PYTHON_FILES} > /dev/null 2>&1 || true
	mypy --strict --ignore-missing-imports ${PYTHON_FILES}
endif

showvars:
	@echo "PYTHON_FILES=${PYTHON_FILES}"
