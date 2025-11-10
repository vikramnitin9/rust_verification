from util import code_extraction_util

import pytest

def test_invalid_json() -> None:
    text = '{ "function_with_specs": " }'
    with pytest.raises(RuntimeError):
        code_extraction_util.extract_function(text)

def test_json_inside_code_fences() -> None:
    text = """```json
    {
        "function_with_specs": "#include <stdio.h> int main() { printf(\\"Hello, world\\"); }"
    }
    ```
    """
    assert code_extraction_util.extract_function(text) == '#include <stdio.h> int main() { printf("Hello, world"); }'

def test_json_inside_code_fences_with_whitespace() -> None:
    text = """
    
    
    
    ```json
    {
        "function_with_specs": "#include <stdio.h> int main() { printf(\\"Hello, world\\"); }"
    }
    ```

    
    """
    assert code_extraction_util.extract_function(text) == '#include <stdio.h> int main() { printf("Hello, world"); }'