from verification import (
    ExternalFunctionDocumentationManager,
    ParsedDocumentation,
    FunctionParameter,
    EntityType,
)

doc_manager = ExternalFunctionDocumentationManager(
    "./verification/docs/ansi_c_library_documentation.json"
)


def test_get_documentation_returns_none() -> None:
    assert doc_manager.get_documentation("fake_function") is None, (
        f"Expected no documnetation for 'fake_function'"
    )


def test_get_documentation_returns_docs() -> None:
    assert doc_manager.get_documentation("aligned_alloc") == ParsedDocumentation(
        entity_type=EntityType.FUNCTION,
        description="Allocate size bytes of uninitialized storage whose alignment is specified by alignment. The size parameter must be an integral multiple of alignment. aligned_alloc is thread-safe: it behaves as though only accessing the memory locations visible through its argument, and not any static storage. A previous call to free or realloc that deallocates a region of memory synchronizes-with a call to aligned_alloc that allocates the same or a part of the same region of memory. This synchronization occurs after any access to the memory by the deallocating function and before any access to the memory by aligned_alloc. There is a single total order of all allocation and deallocation functions operating on each particular region of memory.",
        parameters=[
            FunctionParameter(
                name="alignment",
                description="specifies the alignment. Must be a valid alignment supported by the implementation.",
            ),
            FunctionParameter(
                name="size",
                description="number of bytes to allocate. An integral multiple of alignment",
            ),
        ],
        return_value_description="On success, returns the pointer to the beginning of newly allocated memory. To avoid a memory leak, the returned pointer must be deallocated with free or realloc. On failure, returns a null pointer.",
    )
