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

def test_uncomment_out_cbmc_specs_multi_line_specs() -> None:
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