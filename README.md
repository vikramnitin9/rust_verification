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
python generate_specs.py --file data/qsort.c
```

You can also write a record of the conversation used to generate specifications by passing in the
`--save-conversation` flag:

```sh
python generate_specs.py --file data/qsort.c --save-conversation
```

Which saves the conversation record to `logs/specifications`

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
% bash run.sh python -Xfrozen_modules=off -m debugpy --listen 0.0.0.0:5678 --wait-for-client ./generate_specs.py --file data/qsort.c
```

This effectively starts the container,
  port-forwards it to 5678,
  and suspends execution until the debugger is attached.

Once you have executed the command above,
  select "Python: Attach to Docker" from the "Run and Debug" sidebar.
