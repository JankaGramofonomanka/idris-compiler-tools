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

### Key modules
The entire source code is located in the `lng-compiler/src` and `control-flow/src` folders.

- Data definitions:
  - The `control-flow` package
    - `ControlFlow.CFG` - a representation of a control-flow graph,
      which enforces the correctness of jumps between basic blocks.
    - `ControlFlow.CFG.Simple` - a simplified version if `ControlFlow.CFG`,
      you might want to get familiar with it first
    - `ControlFlow.CBlock` - a representation of a basic block in the process of being constructed,
      i.e., one that facilitates construction of basic blocks from partially defined ones.

  - The `lng-compiler` package
    - `LNG.Parsed` - a representation of `LNG` as it is returned by the **parser**.
      A representation of **syntactically** correct `LNG` code, i.e., the AST tree.
    - `LNG.TypeChecked` - a representation of `LNG` as it is returned by the **type-checker**.
      A **semantically** correct (to the extent it is worth it to enforce) `LNG` code.
    - `LLVM` - a representation of the `LLVM` intermediate representation,
      that takes the role of the target language.

- The compiler (`lng-compiler` package):
  - `Main` - the main program of the compiler.
  - `Parse.Parse`, `Parse.[...]` - the parsing phase of the compiler.
  - `TypeCheck`, `TypeCheck.[...]` - the type-checking phase of the compiler.
  - `Compile`, `Compile.[...]` - the code-generating phase of the compiler.

### The `LNG` language

The `LNG` language is a simple typed imperative language.
It has three data types (four including `void`): `boolean`, `int`, and `string`.
It supports basic arithmetic, boolean logic, if-then-else statements, while loops,
and allows defining and calling functions.

You can see examples of `LNG` programs in the `test` folder.

## How to run the compiler

### Dependencies

#### Package manager
This project is built using the `pack` package manager:
https://github.com/stefan-hoeck/idris2-pack

#### LLVM
To run the code generated by the compiler, you will need the LLVM interpreter. You can install it with:
```
sudo apt install llvm
```

### Build the compiler:
```
pack build lng-compiler
```

### Run the compiler
To compile a source file `SOURCE_DIR.lng` run the following:
```
pack run lng-compiler <SOURCE_DIR>.lng <SOURCE_DIR>.ll
```

### Run the compiled code
To execute the compiled file `DIR.ll` run the following
```
./scripts/run <DIR>.ll
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

You can clean the files generated during the compilation and testing:
```
./scripts/clean
```

## Warning

### The parser is slow when input is invalid

Because the parser is based on the list monad,
it is extremely slow to reject input that is not syntactically correct.
