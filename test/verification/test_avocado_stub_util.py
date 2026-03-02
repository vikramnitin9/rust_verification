from verification import avocado_stub_util


def test_stub_renaming() -> None:
    original_name_to_rename_metadata = avocado_stub_util.get_stub_mappings()
    assert len(original_name_to_rename_metadata) != 0, f"Expected a non-zero number of stub function renamings"

    for original_name, rename_metadata in original_name_to_rename_metadata.items():
        expected_rename = f"avocado_{original_name}"

        assert rename_metadata.avocado_name == expected_rename, (
            f"Expected {original_name} in {rename_metadata.original_file_path.name} to be renamed to: {expected_rename}"
        )
