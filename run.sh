# Check if Docker is rootless.
# If so, run the container with root user to avoid permission issues with mounted volumes.
if docker info -f "{{println .SecurityOptions}}" | grep -q rootless; then
    echo "Docker running in rootless mode"
    docker run --rm -u 0:0 -v $(pwd):/app -it cbmc /bin/bash
else
    docker run --rm -v $(pwd):/app -it cbmc /bin/bash
fi