# Rust verification

Ensure your system has [all requirements](./REQUIREMENTS.md) installed before
  proceeding with the steps below.

First initialize and update submodules:

```sh
git submodule update --init
```

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
make run
# Inside the container:
./main.py --input-path data/qsort.c
```

For a more complex example, we include the [Zopfli](https://github.com/google/zopfli) compression library as a submodule in our data directory. It consists of over 3000 lines of C code across multiple files.

To run specification generation on a project with multiple files, one first needs to generate a JSON compilation database. If your project uses `make`, a simple way to generate a compilation database is to use [`bear`](https://github.com/rizsotto/Bear). Again from inside the container, run:

```sh
# To generate a compile_commands.json compilation database
cd /app/data/zopfli && make clean && bear -- make
```

Verify that `compile_commands.json` now exists at `/app/data/zopfli`. Now generate specifications:

```sh
cd /app
./main.py --input-path data/zopfli
```

## Step 2: Converting C (CProver) specifications to Rust (Kani)

TODO

## Step 3: Translating the C program to Rust

Using any off-the-shelf translator.

## Step 4: Verifying the Rust specifications

Kani is installed in the Docker container. Here is an example of how to run it.

```sh
make run
# Inside the container:
cd data/rust_qsort
cargo kani -Z function-contracts
```

The Kani specifications in `data/rust_qsort/main.rs` are incomplete and currently do not compile. This needs work.

## Tests

```sh
make test
```

## Debugging

Add the following to your `.vscode/launch.json` configuration,
  or check that it already exists:

```json
{
    "name": "Python: Attach to Docker",
    "type": "debugpy",
    "request": "attach",
    "connect": {
        "host": "localhost",
        "port": 5678
    },
    "pathMappings": [
        {
            "localRoot": "${workspaceFolder}",
            "remoteRoot": "/app"
        }
    ],
    "justMyCode": true
}
```

To debug a specification generation run (e.g., for `data/qsort.c`),
  first run the following command:

```sh
% bash run.sh python -Xfrozen_modules=off -m debugpy --listen 0.0.0.0:5678 --wait-for-client ./main.py data/qsort.c
```

This effectively starts the container,
  port-forwards it to 5678,
  and suspends execution until the debugger is attached.

Once you have executed the command above,
  select "Python: Attach to Docker" from the "Run and Debug" sidebar.

## FAQs

> My local runs of `make checks` are inconsistent with those on CI, what's going on?

This is usually due to inconsistencies between your local development dependencies,
  and those on GitHub CI.
Run the following command (periodically, if the issue persists) to update your local dependencies:

```sh
% make plume-scripts-update
```
