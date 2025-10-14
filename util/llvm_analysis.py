from typing import Any
from dataclasses import dataclass, field


@dataclass
class LLVMAnalysis:
    enums: list[Any] = field(default_factory=list)
    files: list[str] = field(default_factory=list)
    functions: list["Function"] = field(default_factory=list)


@dataclass
class Function:
    name: str
    num_args: int
    return_type: str
    signature: str
    file_name: str
    start_col: int
    start_line: int
    end_col: int
    end_line: int
    arg_names: list[str] = field(default_factory=list)
    arg_types: list[str] = field(default_factory=list)
    enums: list[Any] = field(default_factory=list)
    functions: list["Function"] = field(default_factory=list)
    llvm_globals: list[Any] = field(default_factory=list)
    structs: list[Any] = field(default_factory=list)
