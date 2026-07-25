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
.PHONY: test
test: tests
tests: unit-test integration-test
