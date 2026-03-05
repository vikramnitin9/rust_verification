from verification import avocado_stub_util


def test_stub_renaming() -> None:
    name_to_rename_metadata = avocado_stub_util.get_stub_mappings()
    assert len(name_to_rename_metadata) != 0, "Expected a non-zero number of stub function renamings"

    for name, rename_metadata in name_to_rename_metadata.items():
        expected_rename = f"_avocado_{name}"

        assert rename_metadata.avocado_name == expected_rename, (
            f"Expected {name} in {rename_metadata.file_path.name} to be renamed to: {expected_rename}"
        )
