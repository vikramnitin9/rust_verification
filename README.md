# Rust verification

To build the Docker container:

```sh
bash build.sh
```

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
