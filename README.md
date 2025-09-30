See the "Algorithm" tab of [this doc](https://docs.google.com/document/d/11Xq5R7BVrrVsvbpRuOIarTEJlAOH74Ykz6wO1LbYj_k/edit?usp=sharing) for an overview of the desired design of this system.

Currently, the Python script has bugs in the implementation of "swapping in" the specifications for each function. This is elaborated upon in the comments in the [source file](generate_specs.py)

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
