from util import code_extraction_util

import pytest

def test_empty_function_tags() -> None:
    text = """<FUNC></FUNC>"""
    with pytest.raises(RuntimeError):
        code_extraction_util.extract_function(text)

def test_empty_code_fences() -> None:
    text = """
    <FUNC>
    ```C
    ```
    </FUNC>
    """
    with pytest.raises(RuntimeError):
        code_extraction_util.extract_function(text)

def test_valid_code_fence() -> None:
    text = """
    <FUNC>
    ```C
    #include <stdio.h>

    int main()
    {
        printf("Hello, world!");
    }
    ```
    </FUNC>
    """
    assert code_extraction_util.extract_function(text) == """#include <stdio.h>

    int main()
    {
        printf("Hello, world!");
    }"""

def test_valid_code_fence_not_c() -> None:
    text = """
    <FUNC>
    ```scala
    @main def(): Unit = println("Hello world!")
    ```
    </FUNC>
    """
    assert code_extraction_util.extract_function(text, code_fence_language="scala") == '@main def(): Unit = println("Hello world!")'

def test_multiple_code_fence_invalid() -> None:
    text = """
    <FUNC>
    ```c
    #include <stdio.h>

    int main()
    {
        printf("Hello, world!");
    }
    ```

    ```C
    #include <stdio.h>

    int main()
    {
        printf("Hello, world!");
    }
    ```
    </FUNC>
    """
    with pytest.raises(RuntimeError):
        code_extraction_util.extract_function(text)
