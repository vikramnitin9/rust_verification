# Rust verification

Ensure your system has [all requirements](./REQUIREMENTS.md) installed before
  proceeding with the steps below.

To build the Docker container:

```sh
make docker-build
```

## Step 1: Generating C Specifications

To generate specs with an LLM, you first need to put your API key in a `.env` file.

```sh
echo "LLM_API_KEY=<your key here>" > models/.env
```

Then run the Python script

```sh
bash run.sh
# Inside the container:
python generate_specs.py data/qsort.c
```

## Step 2: Converting C (CProver) specifications to Rust (Kani)

TODO

## Step 3: Translating the C program to Rust

Using any off-the-shelf translator.

## Step 4: Verifying the Rust specifications

Kani is installed in the Docker container. Here is an example of how to run it.

```sh
bash run.sh
# Inside the container:
cd data/rust_qsort
cargo kani -Z function-contracts
```

The Kani specifications in `data/rust_qsort/main.rs` are incomplete and currently do not compile. This needs work.

## Tests

```sh
make test
```
