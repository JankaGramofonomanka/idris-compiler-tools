# idris-compiler-tools

## Build the compiler:
```
idris2 --build compiler-tools.ipkg
```

## Run the compiler
To compile a source file `SOURCE_DIR.lat` run the following:
```
./build/exec/compile <SOURCE_DIR>.lat <SOURCE_DIR>.ll
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



