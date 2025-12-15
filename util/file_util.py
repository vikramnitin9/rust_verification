"""Utilities for working with and manipulating files."""

from pathlib import Path


def copy_file_to_folder(input_file_path: Path, destination_folder_name: str) -> Path:
    """Return the file that is copied from the input file to the destination folder.

    Args:
        input_file_path (Path): The input file path.
        destination_folder_name (str): The destination folder under which to copy the file.

    Returns:
        Path: The file that is copied from the input file to the destination folder.
    """
    output_folder = Path(destination_folder_name)
    output_folder.mkdir(parents=True, exist_ok=True)
    output_file_path = output_folder / input_file_path.name

    # MDE: Why not use `shutil.copy()`?
    content = input_file_path.read_text(encoding="utf-8")
    output_file_path.write_text(content, encoding="utf-8")

    return output_file_path


def ensure_lines_at_beginning(lines_to_insert: list[str], file_path: Path) -> None:
    """Ensure the given lines appear in the given file.

    Each line is only inserted if it is not already present in the file (anywhere, not necessarily
    at the beginning).

    Args:
        lines_to_insert (list[str]): The lines to insert.
        file_path (Path): The file to modify.

    """
    file_content = file_path.read_text(encoding="utf-8")
    existing_lines = [line.strip() for line in file_content.splitlines()]
    lines_to_add = [line for line in lines_to_insert if line.strip() not in existing_lines]
    if lines_to_add:
        updated_file_content = "\n".join(lines_to_add) + "\n" + file_content
        file_path.write_text(updated_file_content, encoding="utf-8")
