# idris-compiler-tools

## About

This project aims to design a framework for safe and convenient compiler construction.
The general approach is to define a set of data types that will represent
both the compiled and the target language elements in such a way
that will make it possible to express, and thus, enforce their key properties.
Dependent types play a key role here.

The two properties that receive the most attention in this project are
the type correctness of the language elements (expressions, instructions, function definitions)
and the correctness of jumps between basic blocks of the target language code.

To test the framework in practice, a compiler of a simple imperative language `LNG` is included in the project.

## Key modules
The entire source code is located in the folder `src`

- Data definitions:
  - `LNG.Parsed` - a representation of `LNG` as it is returned by the **parser**.
    A representation of **syntactically** correct `LNG` code, i.e., the AST tree.
  - `LNG.TypeChecked` - a representation of `LNG` as it is returned by the **type-checker**.
    A **semantically** correct (to the extent it is worth it to enforce) `LNG` code.
  - `LLVM` - a representation of the `LLVM` intermediate representation,
    that takes the role of the target language.
  - `CFG` - a representation of a control-flow graph,
    which enforces the correctness of jumps between basic blocks.
  - `Compile.Data.CBlock` - a representation of a basic block in the process of being constructed,
    i.e., one that facilitates construction of basic blocks from partially defined ones.

- The compiler:
  - `Main` - the main program of the compiler.
  - `LNG.Parse`, `Parse.[...]` - the parsing phase of the compiler.
  - `TypeCheck`, `TypeCheck.[...]` - the type-checking phase of the compiler.
  - `Compile`, `Compile.[...]` - the code-generating phase of the compiler.

## How to run the compiler

### Idris version
This project is built using Idris 2 version `0.5.1-a4b99bd81`

### Build the compiler:
```
idris2 --build compiler-tools.ipkg
```

### Run the compiler
To compile a source file `SOURCE_DIR.lng` run the following:
```
./build/exec/compile <SOURCE_DIR>.lng <SOURCE_DIR>.ll
```

### Run the compiled code
To execute the compiled file `DIR.ll` run the following
```
llvm-link -o out.bc <DIR>.ll lib.ll
lli out.bc
```

### Tests
To compile all test cases run the following:
```
./scripts/compile
```

To test the compiled examples, run the following:
```
./scripts/test
```

## Warning
The parser of the LNG language is broken.
Whenever a function or variable identifier is prefixed by a keyword,
the tokenizer will interpret the prefix as a keyword, and thus the program won't parse.
For example, the instruction
```
int elsewhere = 0;
```
will not parse because the name of the variable starts with `else` which is a keyword.

