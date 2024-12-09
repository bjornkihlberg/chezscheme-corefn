# chezscheme-corefn

PureScript CoreFn to ChezScheme transpiler.

---

## Quickstart

```scheme
(import (chezscheme)
        (only (corefn) transpile-corefn-output-folder))

(let-values ([(stdin stdout stderr pid) (open-process-ports "purs compile --codegen corefn ./src/**/*.purs")])
  (unless (port-eof? stderr)
    (error 'purs
      (call-with-string-output-port
        (lambda (textual-output-port)
          (let loop ()
            (unless (port-eof? stderr)
              (put-char textual-output-port (integer->char (get-u8 stderr)))
              (loop)))
          (let loop ()
            (unless (port-eof? stdout)
              (put-char textual-output-port (integer->char (get-u8 stdout)))
              (loop))))))))

(transpile-corefn-output-folder "./output")

(compile-imported-libraries #t)
(generate-wpo-files #t)
(library-directories '(["." . "."] ["./output" . "./output"]))

(compile-library "./output/Main.scm")

(compile-whole-library "./output/Main.wpo" "./Main.so")
```

1. `(open-process-ports "purs compile --codegen corefn ./src/**/*.purs")` compiles PureScript source into CoreFn
1. `(transpile-corefn-output-folder "./output")` generates Chez Scheme libraries from CoreFn
1. `(compile-imported-libraries #t)` ensures that when one Chez Scheme library is compiled, its imported libraries are also compiled
1. `(generate-wpo-files #t)` ensures that Chez Scheme creates whole program optimization files when compiling
1. `(library-directories '(["." . "."] ["./output" . "./output"]))` adds the `./output` folder as a source folder
1. `(compile-library "./output/Main.scm")` compiles `Main` and its dependencies
1. `(compile-whole-library "./output/Main.wpo" "./Main.so")` bundles `Main` and all its dependencies into a single library into the root project folder

```scheme
(import (chezscheme)
        (Main))

(Main.main 5)
```
`Main.main` can now be used as expected.
