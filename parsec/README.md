# ParseC

```text
# MDE: link to the ParseC project documentation.
# MDE: Whenever your project incorporates other people's code, it is essential to say where it came
# from.  Or, did you write all the code in this directory yourself?  If so, it needs to be
# commented.  And the indentation needs to be made consistent (for example, do not use any tab
# characters).
# MDE: If this is written specifically as part of our project, that should be made clear.  Also
# discuss the relationship to other things named "parsec" and "ParseC", such as
# https://hackage.haskell.org/package/parsec and
# https://parallaxsecond.github.io/parsec-book/parsec_service/build_run.html .
# MDE: Also discuss the relationship to https://libclang.readthedocs.io/
```

ParseC is a LLVM/Clang-based tool to parse a C program (hence the name). It extracts functions, structures, etc. along with their inter-dependencies.

ParseC is built as part of the [Docker image](Dockerfile) for this project. However, it can also be built and run independently.

## Prerequisites

ParseC is intended for use only with Linux. The following utilities and libraries are needed:
- `build-essential`
- `cmake`
- `bear`
- `llvm-14`, `llvm-14-dev`, `llvm-14-tools`, `clang-14`, `libclang-14-dev`

## Build

```sh
mkdir build && cd build
cmake .. && make
```

If compilation is successful, the `parsec` binary will be created in the `build` directory. You can add it to your `PATH`, or access it by its full file path.

## Usage

`parsec` can be run on a single C file, say `hello.c`, as follows:

```sh
parsec hello.c
```

To run it on a full project, you need a `compile_commands.json` compilation database for your project. This can be obtained in a few different ways:
- If your project uses CMake, you can generate one automatically by setting [`CMAKE_EXPORT_COMPILE_COMMANDS`](https://cmake.org/cmake/help/latest/variable/CMAKE_EXPORT_COMPILE_COMMANDS.html).
- If your project uses `make`, you can use the `bear` utility to generate a compilation database:

  ```sh
  bear -- make
  ```

Once you have `compile_commands.json`, you can run `parsec` like this:

```sh
parsec *.c
```

## Output

The output of `parsec` is a single JSON file, `analysis.json`, created in the current working directory. The format of this file is described herein:

```json
# MDE: it is essential to give the meaning of each field, and also the formats of strings.
# Or, cross-reference to where that information is documented.
{
  "files": [],
  "functions": [
    {
      "name": "str",
      "signature": "str",
      "num_args": "int",
      "argTypes": ["str"],
      "argNames": ["str"],
      "returnType": ["str"],
      "filename": "str",
      "startLine": "int",
      "endLine": "int",
      "startCol": "int",
      "endCol": "int",
      "callees": [
        {
          "name": "str"
        }
      ],
      "structs": [
        {
          "name": "str"
        }
      ],
      "enums": [
        {
          "name": "str"
        }
      ],
      "globals": [
        {
          "name": "str"
        }
      ]
    }
  ],
  "structs": [
    {
      "name": "str",
      "filename": "str",
      "startLine": "int",
      "endLine": "int",
      "startCol": "int",
      "endCol": "int"
    }
  ],
  "enums": [
    {
      "name": "str",
      "filename": "str",
      "startLine": "int",
      "endLine": "int",
      "startCol": "int",
      "endCol": "int"
    }
  ],
  "globals": [
    {
      "name": "str",
      "type": "str",
      "filename": "str",
      "startLine": "int",
      "endLine": "int",
      "startCol": "int",
      "endCol": "int",
      "isStatic": "bool"
    }
  ]
}
```

Note that the field `files` is intended to be populated with a list of source files and metadata about each one; however, this functionality is not yet implemented and the `files` field will currently always contain an empty list.

## Options and Customization

`parsec` has two command-line flags, `--add-instr` and `--rename-main`. These are intended for internal use and debugging only.
