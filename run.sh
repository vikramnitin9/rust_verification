if [ -n "${CI:-}" ] || [ ! -t 0 ]; then
    echo "Running in a non-interactive environment"
    INTERACTIVE=""
else
    INTERACTIVE="-it"
fi

if [ "$#" -gt 0 ]; then
    CMD=("$@")
else
    CMD=(/bin/bash)
fi

if ! command -v docker &>/dev/null ; then
  echo "$0: command not found: docker" >&2
  exit 2
fi

# Check if Docker is rootless.
# If so, run the container with root user to avoid permission issues with mounted volumes.
if docker info -f "{{println .SecurityOptions}}" | grep -q rootless; then
    echo "Docker running in rootless mode"
    docker run --rm $INTERACTIVE -u 0:0 -v "$(pwd)/data:/app/data" \
                           -v "$(pwd)/analysis:/app/analysis" \
                           -v "$(pwd)/docs:/app/docs" \
                           -v "$(pwd)/models:/app/models" \
                           -v "$(pwd)/specifications:/app/specifications" \
                           -v "$(pwd)/test:/app/test" \
                           -v "$(pwd)/translation:/app/translation" \
                           -v "$(pwd)/util:/app/util" \
                           -v "$(pwd)/verification:/app/verification" \
                           -v "$(pwd)/specs:/app/specs" \
                           -v "$(pwd)/prompt.txt:/app/prompt.txt" \
                           -v "$(pwd)/repair-prompt-template.txt:/app/repair-prompt-template.txt" \
                           -v "$(pwd)/generate_specs.py:/app/generate_specs.py" \
                           cbmc:latest "${CMD[@]}"
else
    docker run --rm $INTERACTIVE -v "$(pwd)/data:/app/data" \
                    -v "$(pwd)/analysis:/app/analysis" \
                    -v "$(pwd)/docs:/app/docs" \
                    -v "$(pwd)/models:/app/models" \
                    -v "$(pwd)/specifications:/app/specifications" \
                    -v "$(pwd)/test:/app/test" \
                    -v "$(pwd)/translation:/app/translation" \
                    -v "$(pwd)/util:/app/util" \
                    -v "$(pwd)/verification:/app/verification" \
                    -v "$(pwd)/specs:/app/specs" \
                    -v "$(pwd)/prompt.txt:/app/prompt.txt" \
                    -v "$(pwd)/repair-prompt-template.txt:/app/repair-prompt-template.txt" \
                    -v "$(pwd)/generate_specs.py:/app/generate_specs.py" \
                    cbmc:latest "${CMD[@]}"
fi
