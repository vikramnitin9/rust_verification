from util import text_util

def test_comment_out_no_specs() -> None:
    lines = [
        "int partition(int arr[], int low, int high)\n",
        "{\n",
        "    int pivot = arr[high];\n",
        "    int i = low - 1;\n",
        "\n",
        "    for (int j = low; j <= high - 1; j++) {\n",
        "        if (arr[j] <= pivot) {\n",
        "            i++;\n",
        "            swap(&arr[i], &arr[j]);\n",
        "        }\n",
        "    }\n",
        "    swap(&arr[i + 1], &arr[high]);\n",
        "    return i + 1;\n",
        "}\n"
    ]
    lines_with_commented_out_specs = text_util.comment_out_cbmc_annotations(lines)
    assert lines_with_commented_out_specs == lines

def test_comment_out_cbmc_specs_multi_line_specs() -> None:
    lines = [
        "int partition(int arr[], int low, int high)\n",
        "__CPROVER_requires(\n",
        "  __CPROVER_is_fresh(arr, (high + 1) * sizeof(*arr)))\n",
        "__CPROVER_requires(low >=\n",
        "0 && high >= low)\n",
        "__CPROVER_ensures(\n",
        "      __CPROVER_return_value >= low &&\n",
        "      __CPROVER_return_value <= high\n",
        ")\n",
        "__CPROVER_ensures(\n",
        "  __CPROVER_forall { int k; (low <= k && \n",
        "        k < __CPROVER_return_value) ==> (arr[k] <=\n",
        "        arr[__CPROVER_return_value]) })\n",
        "__CPROVER_ensures(__CPROVER_forall { int k; (__CPROVER_return_value < k && k <= high) ==> (arr[k] > arr[__CPROVER_return_value]) })\n",
        "{\n",
        "    int pivot = arr[high];\n",
        "    int i = low - 1;\n",
        "\n",
        "    for (int j = low; j <= high - 1; j++) {\n",
        "        if (arr[j] <= pivot) {\n",
        "            i++;\n",
        "            swap(&arr[i], &arr[j]);\n",
        "        }\n",
        "    }\n",
        "    swap(&arr[i + 1], &arr[high]);\n",
        "    return i + 1;\n",
        "}\n"
    ]
    lines_with_commented_out_specs = text_util.comment_out_cbmc_annotations(lines)
    assert lines_with_commented_out_specs == [
        "int partition(int arr[], int low, int high)\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(\n",
        f"{text_util.CBMC_COMMENT_PREFIX}  __CPROVER_is_fresh(arr, (high + 1) * sizeof(*arr)))\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(low >=\n",
        f"{text_util.CBMC_COMMENT_PREFIX}0 && high >= low)\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(\n",
        f"{text_util.CBMC_COMMENT_PREFIX}      __CPROVER_return_value >= low &&\n",
        f"{text_util.CBMC_COMMENT_PREFIX}      __CPROVER_return_value <= high\n",
        f"{text_util.CBMC_COMMENT_PREFIX})\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(\n",
        f"{text_util.CBMC_COMMENT_PREFIX}  __CPROVER_forall {{ int k; (low <= k && \n",
        f"{text_util.CBMC_COMMENT_PREFIX}        k < __CPROVER_return_value) ==> (arr[k] <=\n",
        f"{text_util.CBMC_COMMENT_PREFIX}        arr[__CPROVER_return_value]) }})\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(__CPROVER_forall {{ int k; (__CPROVER_return_value < k && k <= high) ==> (arr[k] > arr[__CPROVER_return_value]) }})\n",
        "{\n",
        "    int pivot = arr[high];\n",
        "    int i = low - 1;\n",
        "\n",
        "    for (int j = low; j <= high - 1; j++) {\n",
        "        if (arr[j] <= pivot) {\n",
        "            i++;\n",
        "            swap(&arr[i], &arr[j]);\n",
        "        }\n",
        "    }\n",
        "    swap(&arr[i + 1], &arr[high]);\n",
        "    return i + 1;\n",
        "}\n"
    ]


def test_comment_out_cbmc_specs_single_line_specs() -> None:
    lines = [
        "void swap(int* a, int* b) \n",
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(*a))) \n",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(*b))) \n",
        "__CPROVER_ensures(*a == __CPROVER_old(*b) && *b == __CPROVER_old(*a)) \n",
        "__CPROVER_assigns(*a, *b) \n",
        "{\n",
        "    int t = *a;\n",
        "    *a = *b;\n",
        "    *b = t;\n",
        "}\n"
    ]
    lines_with_commented_out_specs = text_util.comment_out_cbmc_annotations(lines)
    assert lines_with_commented_out_specs == [
        "void swap(int* a, int* b) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(*a))) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(*b))) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(*a == __CPROVER_old(*b) && *b == __CPROVER_old(*a)) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_assigns(*a, *b) \n",
        "{\n",
        "    int t = *a;\n",
        "    *a = *b;\n",
        "    *b = t;\n",
        "}\n"
    ]

def test_uncomment_cbmc_specs_single_line() -> None:
    lines_with_commented_out_specs = [
        "void swap(int* a, int* b) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(*a))) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(*b))) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(*a == __CPROVER_old(*b) && *b == __CPROVER_old(*a)) \n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_assigns(*a, *b) \n",
        "{\n",
        "    int t = *a;\n",
        "    *a = *b;\n",
        "    *b = t;\n",
        "}\n"
    ]
    lines_with_specs = [
        "void swap(int* a, int* b) \n",
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(*a))) \n",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(*b))) \n",
        "__CPROVER_ensures(*a == __CPROVER_old(*b) && *b == __CPROVER_old(*a)) \n",
        "__CPROVER_assigns(*a, *b) \n",
        "{\n",
        "    int t = *a;\n",
        "    *a = *b;\n",
        "    *b = t;\n",
        "}\n"
    ]
    assert lines_with_specs == text_util.uncomment_cbmc_annotations(lines_with_commented_out_specs)

def test_uncomment_cbmc_specs_multi_line_specs() -> None:
    lines_with_commented_out_specs = [
        "int partition(int arr[], int low, int high)\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(\n",
        f"{text_util.CBMC_COMMENT_PREFIX}  __CPROVER_is_fresh(arr, (high + 1) * sizeof(*arr)))\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_requires(low >=\n",
        f"{text_util.CBMC_COMMENT_PREFIX}0 && high >= low)\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(\n",
        f"{text_util.CBMC_COMMENT_PREFIX}      __CPROVER_return_value >= low &&\n",
        f"{text_util.CBMC_COMMENT_PREFIX}      __CPROVER_return_value <= high\n",
        f"{text_util.CBMC_COMMENT_PREFIX})\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(\n",
        f"{text_util.CBMC_COMMENT_PREFIX}  __CPROVER_forall {{ int k; (low <= k && \n",
        f"{text_util.CBMC_COMMENT_PREFIX}        k < __CPROVER_return_value) ==> (arr[k] <=\n",
        f"{text_util.CBMC_COMMENT_PREFIX}        arr[__CPROVER_return_value]) }})\n",
        f"{text_util.CBMC_COMMENT_PREFIX}__CPROVER_ensures(__CPROVER_forall {{ int k; (__CPROVER_return_value < k && k <= high) ==> (arr[k] > arr[__CPROVER_return_value]) }})\n",
        "{\n",
        "    int pivot = arr[high];\n",
        "    int i = low - 1;\n",
        "\n",
        "    for (int j = low; j <= high - 1; j++) {\n",
        "        if (arr[j] <= pivot) {\n",
        "            i++;\n",
        "            swap(&arr[i], &arr[j]);\n",
        "        }\n",
        "    }\n",
        "    swap(&arr[i + 1], &arr[high]);\n",
        "    return i + 1;\n",
        "}\n"
    ]
    lines_with_specs = [
        "int partition(int arr[], int low, int high)\n",
        "__CPROVER_requires(\n",
        "  __CPROVER_is_fresh(arr, (high + 1) * sizeof(*arr)))\n",
        "__CPROVER_requires(low >=\n",
        "0 && high >= low)\n",
        "__CPROVER_ensures(\n",
        "      __CPROVER_return_value >= low &&\n",
        "      __CPROVER_return_value <= high\n",
        ")\n",
        "__CPROVER_ensures(\n",
        "  __CPROVER_forall { int k; (low <= k && \n",
        "        k < __CPROVER_return_value) ==> (arr[k] <=\n",
        "        arr[__CPROVER_return_value]) })\n",
        "__CPROVER_ensures(__CPROVER_forall { int k; (__CPROVER_return_value < k && k <= high) ==> (arr[k] > arr[__CPROVER_return_value]) })\n",
        "{\n",
        "    int pivot = arr[high];\n",
        "    int i = low - 1;\n",
        "\n",
        "    for (int j = low; j <= high - 1; j++) {\n",
        "        if (arr[j] <= pivot) {\n",
        "            i++;\n",
        "            swap(&arr[i], &arr[j]);\n",
        "        }\n",
        "    }\n",
        "    swap(&arr[i + 1], &arr[high]);\n",
        "    return i + 1;\n",
        "}\n"
    ]
    assert lines_with_specs == text_util.uncomment_cbmc_annotations(lines_with_commented_out_specs)

def test_count_suffix_no_matches() -> None:
    text = """/app/specs/qsort.c function swap
        [swap.pointer_dereference.2] line 7 dereference failure: pointer invalid in *a: UNKNOWN
        [swap.pointer_dereference.3] line 7 dereference failure: deallocated dynamic object in *a: UNKNOWN
        [swap.pointer_dereference.4] line 7 dereference failure: dead object in *a: UNKNOWN
        [swap.pointer_dereference.6] line 7 dereference failure: invalid integer address in *a: UNKNOWN
        [swap.pointer_dereference.8] line 8 dereference failure: pointer invalid in *b: UNKNOWN
        [swap.pointer_dereference.9] line 8 dereference failure: deallocated dynamic object in *b: UNKNOWN
        [swap.pointer_dereference.10] line 8 dereference failure: dead object in *b: UNKNOWN
        [swap.pointer_dereference.12] line 8 dereference failure: invalid integer address in *b: UNKNOWN

        ** 0 of 69 failed (4 iterations)
        VERIFICATION FAILED"""
    assert 0 == text_util.count_lines_with_suffix(text, suffix="FAILURE")

def test_count_suffix_matches() -> None:
    text = """/app/specs/qsort.c function swap
        [swap.pointer_dereference.1] line 7 dereference failure: pointer NULL in *a: FAILURE
        [swap.pointer_dereference.2] line 7 dereference failure: pointer invalid in *a: UNKNOWN
        [swap.pointer_dereference.3] line 7 dereference failure: deallocated dynamic object in *a: UNKNOWN
        [swap.pointer_dereference.4] line 7 dereference failure: dead object in *a: UNKNOWN
        [swap.pointer_dereference.5] line 7 dereference failure: pointer outside object bounds in *a: FAILURE
        [swap.pointer_dereference.6] line 7 dereference failure: invalid integer address in *a: UNKNOWN
        [swap.assigns.1] line 8 Check that *a is assignable: FAILURE
        [swap.pointer_dereference.7] line 8 dereference failure: pointer NULL in *b: FAILURE
        [swap.pointer_dereference.8] line 8 dereference failure: pointer invalid in *b: UNKNOWN
        [swap.pointer_dereference.9] line 8 dereference failure: deallocated dynamic object in *b: UNKNOWN
        [swap.pointer_dereference.10] line 8 dereference failure: dead object in *b: UNKNOWN
        [swap.pointer_dereference.11] line 8 dereference failure: pointer outside object bounds in *b: FAILURE
        [swap.pointer_dereference.12] line 8 dereference failure: invalid integer address in *b: UNKNOWN

        ** 5 of 69 failed (4 iterations)
        VERIFICATION FAILED"""
    assert 5 == text_util.count_lines_with_suffix(text, suffix="FAILURE")