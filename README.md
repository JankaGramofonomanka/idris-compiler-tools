# idris-compiler-tools

## Idris version
This project is built using Idris 2 version `0.5.1-a4b99bd81`

## Build the compiler:
```
idris2 --build compiler-tools.ipkg
```

## Run the compiler
To compile a source file `SOURCE_DIR.lng` run the following:
```
./build/exec/compile <SOURCE_DIR>.lng <SOURCE_DIR>.ll
```

## Run the compiled code
To execute the compiled file `DIR.ll` run the following
```
llvm-link -o out.bc <DIR>.ll lib.ll
lli out.bc
```

## Tests
To compile all test cases run the following:
```
./scripts/compile
```

To test the compiled examples, run the following:
```
./scripts/test
```



