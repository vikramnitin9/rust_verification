import pytest

from util import code_extraction_util
from util import FunctionSpecification


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


def test_extract_specs_empty_specs() -> None:
    text = """
    {
        "preconditions": [],
        "postconditions": []
    }
    """
    assert code_extraction_util.parse_specs(text) == None, (
        f"A response with empty pre and postconditions cannot be parsed into a valid specification"
    )


def test_extract_specs_empty_preconditions() -> None:
    text = """
    {
        "preconditions": [],
        "postconditions": ["__CPROVER_assigns(*out)"]
    }
    """
    assert code_extraction_util.parse_specs(text) == FunctionSpecification(
        preconditions=[], postconditions=["__CPROVER_assigns(*out)"]
    )


def test_extract_specs_empty_postconditions() -> None:
    text = """
    {
        "preconditions": ["__CPROVER_requires(a > 0)"],
        "postconditions": []
    }
    """
    assert code_extraction_util.parse_specs(text) == FunctionSpecification(
        preconditions=["__CPROVER_requires(a > 0)"], postconditions=[]
    )


def test_extract_specs_malformed_response() -> None:
    text = """
    {
        "not_valid": ["__CPROVER_requires(a > 0)"],
        "nonsense": []
    }
    """
    assert code_extraction_util.parse_specs(text) == None


def test_extract_specs_well_formed_response() -> None:
    text = """
    {
        "preconditions": ["__CPROVER_requires(a > 0)"],
        "postconditions": ["__CPROVER_ensures(__CPROVER_return_value != 0)", "__CPROVER_ensures(a > 0)"]
    }
    """
    assert code_extraction_util.parse_specs(text) == FunctionSpecification(
        preconditions=["__CPROVER_requires(a > 0)"],
        postconditions=[
            "__CPROVER_ensures(__CPROVER_return_value != 0)",
            "__CPROVER_ensures(a > 0)",
        ],
    )
