# chezscheme-corefn

PureScript CoreFn to ChezScheme transpiler.

---

## Quickstart

#### `src/Main.purs`

```haskell
module Main where

main :: Int -> Int
main _ = 7
```

#### `build.scm`

```lisp
(import (only (corefn) transpile-corefn-output-folder))

(define output-dir "./output")

(unless (file-directory? output-dir) (mkdir output-dir))

(assert (zero? (system (format "cp ./prim.scm ~a" output-dir))))

(assert (zero? (system (format "purs compile -o ~a -g corefn --source-globs-file ./sourcefiles.txt" output-dir))))

(transpile-corefn-output-folder output-dir)

(compile-imported-libraries #t)
(generate-wpo-files #t)
(library-directories `(["." . "."] [,output-dir . ,output-dir]))

(compile-library "./output/Main.scm")

(compile-whole-library "./output/Main.wpo" "./Main.so")
```

```
$ scheme --script build.scm
```

#### `app.scm`

```lisp
(import (chezscheme)
        (Main))

(pretty-print (Main.main 5))
```

```
$ scheme --libdirs .:./output --program app.scm

7
```
