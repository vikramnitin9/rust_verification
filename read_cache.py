#!/opt/miniconda3/bin/python
# ruff: noqa

from diskcache import Cache  # ty: ignore

VERIFIER_CACHE_PATH = "data/caching/verifier"


def main() -> None:
    verifier_cache = Cache(directory=VERIFIER_CACHE_PATH)
    for key in verifier_cache.iterkeys():
        vresult = verifier_cache[key]
        if vresult.succeeded:
            verified_spec = vresult.get_spec()
            print(f"Function name = '{vresult.get_function().name}'")
            print(f"Spec = {verified_spec}")


if __name__ == "__main__":
    main()
