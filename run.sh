# Check if Docker is rootless.
# If so, run the container with root user to avoid permission issues with mounted volumes.
if docker info -f "{{println .SecurityOptions}}" | grep -q rootless; then
    echo "Docker running in rootless mode"
    docker run --rm -u 0:0 -v $(pwd)/data:/app/data \
                           -v $(pwd)/docs:/app/docs \
                           -v $(pwd)/models:/app/models \
                           -v $(pwd)/util:/app/util \
                           -v $(pwd)/specs:/app/specs \
                           -v $(pwd)/prompt.txt:/app/prompt.txt \
                           -v $(pwd)/generate_specs.py:/app/generate_specs.py \
                           -it cbmc:latest /bin/bash
else
    docker run --rm -v $(pwd)/data:/app/data \
                    -v $(pwd)/docs:/app/docs \
                    -v $(pwd)/models:/app/models \
                    -v $(pwd)/util:/app/util \
                    -v $(pwd)/specs:/app/specs \
                    -v $(pwd)/prompt.txt:/app/prompt.txt \
                    -v $(pwd)/generate_specs.py:/app/generate_specs.py \
                    -it cbmc:latest /bin/bash
fi