"""Script to translate CBMC specifications to their Kani equivalents."""

import argparse


def main() -> None:
    """Entry point for CBMC specification translation to Kani."""
    parser = argparse.ArgumentParser(
        description="A script to translate CBMC specifications to their Kani equivalents."
    )
    parser.add_argument(
        "--file",
        help="The file containing C functions with CBMC specifications to translate into Kani"
        "specifications.",
    )


if __name__ == "__main__":
    main()
