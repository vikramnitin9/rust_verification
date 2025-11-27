from util import text_util

def test_get_text_with_prefix_no_results():
    text = """
    Test
    Hello
    world
    """
    assert text_util.get_lines_with_suffix(text, suffix="no_suffix") == []

def test_get_text_with_prefix_results():
    text = """
    this line ends with a suffix
    prefix this line does not end with
    suffix
    """
    assert text_util.get_lines_with_suffix(text, "suffix") == ["this line ends with a suffix", "suffix"]

def test_get_text_with_prefix_whitespace():
    text = """
    this line ends with a suffix  
    prefix this line does not end with
    suffix     
    """
    assert text_util.get_lines_with_suffix(text, "suffix") == ["this line ends with a suffix", "suffix"]
