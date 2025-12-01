"""Utilities for working with and manipulating files."""

from pathlib import Path


def copy_file_to_folder(input_file_path: Path, destination_folder_name: str) -> Path:
    """Return the path to the file that is copied from the input file to the destination folder.

    Args:
        input_file_path (Path): The input file path.
        destination_folder_name (str): The destination folder under which to copy the file.

    Returns:
        Path: The path to the file that is copied from the input file to the destination folder.
    """
    output_folder = Path(destination_folder_name)
    output_folder.mkdir(exist_ok=True)
    output_file_path = output_folder / input_file_path.name

    content = input_file_path.read_text(encoding="utf-8")
    output_file_path.write_text(content, encoding="utf-8")

    return output_file_path


def insert_lines_at_beginning(lines_to_insert: list[str], file_path: Path) -> None:
    """Insert the given lines at the beginning of the file specified at the path.

    The lines are only inserted if they are not already present in the file.

    Args:
        lines_to_insert (list[str]): The lines to insert.
        file_path (Path): The path to the file to modify.
    """
    file_content = file_path.read_text(encoding="utf-8")
    existing_lines = [line.strip() for line in file_content.splitlines()]
    for line_to_insert in lines_to_insert:
        if line_to_insert not in existing_lines:
            file_content = f"{line_to_insert}\n{file_content}"
    file_path.write_text(file_content, encoding="utf-8")


def overwrite_file(content: str, path_to_file_to_overwrite: Path) -> None:
    """Overwrite the file at the given path with the content.

    Args:
        content (str): The content with which to overwrite the file.
        path_to_file_to_overwrite (Path): The path to the file to overwrite.
    """
    Path(path_to_file_to_overwrite).write_text(content, encoding="utf-8")
