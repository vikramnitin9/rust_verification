import pytest

from util import code_extraction_util


def test_extract_function_source_code_invalid_json() -> None:
    text = '{ "function_with_specs": " }'
    with pytest.raises(RuntimeError):
        code_extraction_util.extract_function_source_code(text)


def test_extract_function_source_code_json_inside_code_fences() -> None:
    text = """```json
    {
        "function_with_specs": "#include <stdio.h> int main() { printf(\\"Hello, world\\"); }"
    }
    ```
    """
    assert (
        code_extraction_util.extract_function_source_code(text)
        == '#include <stdio.h> int main() { printf("Hello, world"); }'
    )


def test_extract_function_source_code_json_inside_code_fences_with_whitespace() -> None:
    text = """
    
    
    
    ```json
    {
        "function_with_specs": "#include <stdio.h> int main() { printf(\\"Hello, world\\"); }"
    }
    ```


    """
    assert (
        code_extraction_util.extract_function_source_code(text)
        == '#include <stdio.h> int main() { printf("Hello, world"); }'
    )


def test_extract_function_source_code_plain_json() -> None:
    text = """
    {
        "function_with_specs": "#include <stdio.h> int main() { printf(\\"Hello, world\\"); }"
    }
    """
    assert (
        code_extraction_util.extract_function_source_code(text)
        == '#include <stdio.h> int main() { printf("Hello, world"); }'
    )
