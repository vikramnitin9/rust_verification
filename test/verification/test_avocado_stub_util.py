from verification import avocado_stub_util


def test_stub_renaming() -> None:
    name_to_rename_data = avocado_stub_util.get_stub_mappings()
    assert len(name_to_rename_data) != 0, "Expected a non-zero number of stub function renamings"

    for name, rename_data in name_to_rename_data.items():
        expected_rename = f"_avocado_{name}"

        assert rename_data.avocado_name == expected_rename, (
            f"Expected {name} in {rename_data.file_path.name} to be renamed to: {expected_rename}"
        )
