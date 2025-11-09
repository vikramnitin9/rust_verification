"""Utility functions for extracting source code from text."""

import re


def extract_function(text: str, function_tag: str = "FUNC", code_fence_language: str = "c") -> str:
    """Return the part of a string inside a set of code fences, delimited by function tags.

    Args:
        text (str): The text from which to extract a function.
        function_tag (str, optional): The tag delimiting code fences. Defaults to "FUNC".
        code_fence_language (str, optional): The code fence language. Defaults to "c".

    Raises:
        RuntimeError: Raised when the text does not contain function tags, or does not contain
            exactly one code fence with the given language.

    Returns:
        str: The part of a string inside a set of code fences, delimited by function tags.
    """
    print(f"RESPONSE IS = {text}\n\n")
    open_tag = f"<{function_tag}>"
    close_tag = f"</{function_tag}>"

    # Use f-string or re.escape to build the regex pattern dynamically
    tag_capture_pattern = rf"{re.escape(open_tag)}(.*?){re.escape(close_tag)}"
    code_fences = re.findall(tag_capture_pattern, text, re.DOTALL)

    if len(code_fences) != 1:
        msg = f"Wrong number of functions {len(code_fences)}: {code_fences}"
        raise RuntimeError(msg)
    code_fence = code_fences[0]
    fences = re.findall(r"```", code_fence)
    if not fences or len(fences) != 2:
        msg = f"Expected one set of code fences, but found {len(fences) // 2}"
        raise RuntimeError(msg)
    language_specifier = (
        f"{code_fence_language.lower()}|"
        f"{code_fence_language.upper()}|{code_fence_language.capitalize()}"
    )
    match = re.search(rf"```(?:{language_specifier})?(.*)```", code_fence, re.DOTALL)
    if not match:
        raise RuntimeError("Existing fences not found: " + code_fence)
    code_inside_fence = match.group(1)
    if code_inside_fence.isspace():
        msg = "The part between the code fence was empty"
        raise RuntimeError(msg)
    return code_inside_fence.strip()
