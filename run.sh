docker run -it --rm
    -v "$(pwd)":/app
    /bin/bash -c "goto-cc -o qsort.goto qsort_specs.c --function quickSort"
