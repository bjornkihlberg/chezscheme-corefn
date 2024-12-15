#!chezscheme

(library (corefn)
  (export transpile-corefn-output-folder)

  (import (chezscheme))

  (module (dbg)
    (define-syntax (dbg code)
      (syntax-case code ()
        [(_ e)
          (let ([ann (syntax->annotation #'e)])
            (if ann
                (let-values ([(file line column) (locate-source-object-source (annotation-source ann) #t #f)])
                  #`(let ([x e])
                      (format #t "\x1B;[33mdbg in ~s on line ~s, character ~s\x1B;[0m: ~s\n" #,file #,line #,column x)
                      x))
                #`(let ([x e])
                    (format #t "\x1B;[33mdbg: ~s\x1B;[0m\n" x)
                    x)))])))

  (module (hashtable-map-values assq->symbol-hashtable)
    (define (assq->symbol-hashtable ks/vs)
      (let ([hashtable (make-hashtable symbol-hash symbol=? (length ks/vs))])
        (for-each (lambda (k/v) (symbol-hashtable-set! hashtable (car k/v) (cdr k/v))) ks/vs)
        hashtable))

    (define (hashtable-map-values f hashtable)
      (let ([result (hashtable-copy hashtable #t)])
        (let-values ([(ks vs) (hashtable-entries hashtable)])
          (vector-for-each (lambda (k v) (symbol-hashtable-set! result k (f v))) ks vs)
          result))))

  (module (read-json)
    (module (<- monad)
      (define-syntax (<- code) (syntax-error code "misplaced aux keyword"))

      (define-syntax monad
        (syntax-rules (<- let let* letrec let-values let*-values)
          [(_ flat-map mx) mx]
          [(_ flat-map (<- x mx) body+ ...) (flat-map (lambda (x) (monad flat-map body+ ...)) mx)]
          [(_ flat-map mx body+ ...)        (flat-map (lambda (x) (monad flat-map body+ ...)) mx)])))

    (module (stream-null
            stream-null?
            stream-car
            stream-cdr
            stream-filter
            input-port->stream)

      (define (stream-null) '())

      (define-syntax stream
        (syntax-rules ()
          [(_) stream-null]
          [(_ e e* ...) (delay (cons e (stream e* ...)))]))

      (define (stream-pair? xs)
        (pair? (xs)))

      (define (stream-null? xs)
        (null? (xs)))

      (define (stream-car xs)
        (car (xs)))

      (define (stream-cdr xs)
        (cdr (xs)))

      (define (stream-filter f xs)
        (let loop ([xs xs])
          (delay
            (if (stream-null? xs)
                (stream-null)
                (if (f (stream-car xs))
                    (cons (stream-car xs)
                          (loop (stream-cdr xs)))
                    ((loop (stream-cdr xs))))))))

      (define (input-port->stream tip)
        (if (textual-port? tip)
            (let loop () (delay (if (port-eof? tip) '() (cons (get-char tip) (loop)))))
            (let loop () (delay (if (port-eof? tip) '() (cons (get-u8   tip) (loop))))))))

    (module (parser-end
            parser-any
            parser-peek
            parser-many
            parser-until
            parser-alt
            parser-const
            parser-try
            parser-map
            parser-pure
            parser-flat-map
            parser-satisfies
            parser-satisfies-eq?
            parser-seq-string
            parser-run*)

      (define (parser-end state on-success on-failure)
        (if (stream-null? state)
            (on-success #!eof state)
            (on-failure state)))

      (define (parser-any state on-success on-failure)
        (if (stream-null? state)
            (on-failure state)
            (on-success (stream-car state) (stream-cdr state))))

      (define (parser-peek parser)
        (lambda (state on-success on-failure)
          (parser state
            (lambda (value next-state) (on-success value state))
            on-failure)))

      (define parser-many
        (case-lambda
          [(parser) (parser-many 0 parser)]
          [(at-least parser) (parser-many at-least #f parser)]
          [(at-least at-most parser)
            (lambda (state on-success on-failure)
              (let loop ([state state] [acc '()] [n 0])
                (if (and at-most (fx>= n at-most))
                    (on-success (reverse acc) state)
                    (if (fx>= n at-least)
                      (parser state
                        (lambda (value state) (loop state (cons value acc) (add1 n)))
                        (lambda (next-state) (on-success (reverse acc) state)))
                      (parser state
                        (lambda (value state) (loop state (cons value acc) (add1 n)))
                        on-failure)))))]))

      (define (parser-until parser)
        (lambda (state on-success on-failure)
          (let loop ([state state] [acc '()])
            (parser state
              (lambda (value state) (on-success (cons (reverse acc) value) state))
              (lambda (state) (loop (stream-cdr state) (cons (stream-car state) acc)))))))

      (define parser-alt
        (case-lambda
          [(p) p]
          [(p . ps)
            (lambda (state on-success on-failure)
              (p state
                on-success
                (lambda (next-state)
                  ((apply parser-alt ps) state on-success on-failure))))]))

      (define-syntax parser-const
        (syntax-rules ()
          [(_ x p)
            (lambda (state on-success on-failure)
              (p state
                (lambda (value state) (on-success x state))
                on-failure))]))

      (define parser-try
        (case-lambda
          [(parser) (parser-try parser #f)]
          [(parser default)
            (lambda (state on-success on-failure)
              (parser state
                on-success
                (lambda (next-state) (on-success default state))))]))

      (define (parser-map f parser)
        (lambda (state on-success on-failure)
          (parser state
            (lambda (value state) (on-success (f value) state))
            on-failure)))

      (define (parser-pure value)
        (lambda (state on-success on-failure)
          (on-success value state)))

      (define (parser-flat-map kleisli parser)
        (lambda (state on-success on-failure)
          (parser state
            (lambda (value next-state)
              ((kleisli value) next-state
                on-success
                on-failure))
            on-failure)))

      (define (parser-satisfies predicate)
        (lambda (state on-success on-failure)
          (parser-any state
            (lambda (value next-state)
              (if (predicate value)
                  (on-success value next-state)
                  (on-failure state)))
            on-failure)))

      (define (parser-satisfies-eq? x)
        (parser-satisfies (lambda (y) (eq? x y))))

      (define (parser-seq-string s)
        (let ([n (string-length s)])
          (let loop ([i 0])
            (if (fx>= i n)
                (parser-pure s)
                (parser-flat-map (lambda (_) (loop (add1 i))) (parser-satisfies-eq? (string-ref s i)))))))

      (define (parser-run* input parser on-failure)
        (let loop ([input input])
          (delay
            (if (stream-null? input)
              (stream-null)
              (parser input
                (lambda (value state) (cons value (loop state)))
                on-failure))))))

    (define parse-whitespace-token (parser-const (void) (parser-many 1 (parser-satisfies char-whitespace?))))
    (define parse-null-token       (parser-const 'null  (parser-seq-string "null")))
    (define parse-true-token       (parser-const #t     (parser-seq-string "true")))
    (define parse-false-token      (parser-const #f     (parser-seq-string "false")))
    (define parse-comma-token      (parser-satisfies-eq? #\,))
    (define parse-colon-token      (parser-satisfies-eq? #\:))
    (define parse-openbrace-token  (parser-satisfies-eq? #\{))
    (define parse-closebrace-token (parser-satisfies-eq? #\}))
    (define parse-openbrack-token  (parser-satisfies-eq? #\[))
    (define parse-closebrack-token (parser-satisfies-eq? #\]))
    (define parse-illegal-token    (parser-map (lambda (r) (list 'illegal (apply string (car r)))) (parser-until (parser-peek (parser-alt parser-end (parser-satisfies (lambda (c) (or (char-whitespace? c) (memq c '(#\, #\: #\{ #\} #\[ #\] #\"))))))))))

    (define parse-string-token
      (let ([parse-escape
              (monad parser-flat-map
                (parser-satisfies-eq? #\\)
                (<- c parser-any)
                (parser-pure (case c [#\n #\newline]
                                      [#\r #\return]
                                      [#\t #\tab]
                                      [else c])))]
            [parse-content (parser-satisfies (lambda (x) (not (eq? x #\"))))])
        (monad parser-flat-map
          (parser-satisfies-eq? #\")
          (<- content (parser-many (parser-alt parse-escape parse-content)))
          (parser-satisfies-eq? #\")
          (parser-pure (apply string content)))))

    (define (chars->number negate? digits decimals? exponent?)
      (let ([x (cdr (fold-left
                      (lambda (acc x) (cons (* (car acc) 10) (+ (cdr acc) (* x (car acc)))))
                      (cons 1 0)
                      (reverse (map (lambda (c) (fx- (char->integer c) 48)) digits))))]
            [d (and decimals?
                (cdr
                  (fold-left
                    (lambda (acc x) (cons (* (car acc) 1/10) (+ (cdr acc) (* x (car acc)))))
                    (cons 1/10 0)
                    (map (lambda (c) (fx- (char->integer c) 48)) decimals?))))]
            [e (and exponent? (chars->number (car exponent?) (cdr exponent?) #f #f))])
        (let ([x (if d (+ x d) x)])
          (let ([x (if negate? (* -1 x) x)])
            (let ([x (if e (* x (expt 10 e)) x)])
              (if (or (and (rational-valued? x) (not (integer-valued? x))) decimals?)
                  (real->flonum x)
                  x))))))

    (define parse-number-token
      (monad parser-flat-map
        (<- negate? (parser-try (parser-satisfies-eq? #\-)))
        (<- digit0 (parser-satisfies char-numeric?))
        (<- digits
          (if (char=? digit0 #\0)
              (parser-pure '())
              (parser-many (parser-satisfies char-numeric?))))
        (<- decimals?
          (parser-try
            (monad parser-flat-map
              (parser-satisfies-eq? #\.)
              (parser-many 1 (parser-satisfies char-numeric?)))))
        (<- exponent?
          (parser-try
            (monad parser-flat-map
              (parser-alt (parser-satisfies-eq? #\e) (parser-satisfies-eq? #\E))
              (<- sign? (parser-try (parser-alt (parser-const #f (parser-satisfies-eq? #\+))
                                                  (parser-const #t (parser-satisfies-eq? #\-)))))
              (<- digits (parser-many 1 (parser-satisfies char-numeric?)))
              (parser-pure (cons sign? digits)))))
        (parser-pure (chars->number negate? (cons digit0 digits) decimals? exponent?))))

    (define parse-json-token
      (parser-alt
        parse-whitespace-token
        parse-null-token
        parse-true-token
        parse-false-token
        parse-comma-token
        parse-colon-token
        parse-openbrace-token
        parse-closebrace-token
        parse-openbrack-token
        parse-closebrack-token
        parse-string-token
        parse-number-token
        parse-illegal-token))

    (define (lex-json-document character-stream)
      (stream-filter
        (lambda (token)
          (and (not (and (pair? token) (eq? (car token) 'illegal)))
              (not (memq token '(#\, #\:)))
              (not (eq? token (void)))))
        (parser-run*
          character-stream
          parse-json-token
          (lambda (state) (assert #f)))))

    (define parse-json-datum
      (let ([parse-key/value
              (monad parser-flat-map
                (<- k (parser-satisfies string?))
                (<- v parse-json-datum)
                (parser-pure (cons (string->symbol k) v)))])
        (parser-alt
          (parser-satisfies (lambda (token)
                              (or (string? token)
                                  (boolean? token)
                                  (number? token)
                                  (eq? token 'null))))
          (monad parser-flat-map
            (parser-satisfies-eq? #\[)
            (<- content (parser-many parse-json-datum))
            (parser-satisfies-eq? #\])
            (parser-pure (apply vector content)))
          (monad parser-flat-map
            (parser-satisfies-eq? #\{)
            (<- content (parser-many parse-key/value))
            (parser-satisfies-eq? #\})
            (parser-pure (assq->symbol-hashtable content))))))

    (define (read-json textual-input-port)
      (parse-json-datum (lex-json-document (input-port->stream textual-input-port))
        (lambda (value state) value)
        (lambda (state)
          (if (stream-null? state)
              (assertion-violationf 'read-json "Unexpected end")
              (assertion-violationf 'read-json "Unknown token ~s" (stream-car state)))))))

  (module (match hashtable record)
    (define-syntax (hashtable code) (syntax-error code "misplaced aux keyword"))
    (define-syntax (record code) (syntax-error code "misplaced aux keyword"))

    (define-syntax (when-match code)
      (syntax-case code (quasiquote unquote unquote-splicing)
        [(_ v p e e* ...) (not (atom? (datum v)))
          #'(let ([v0 v]) (when-match v0 p e e* ...))]

        [(_ v p e e* ...) (and (identifier? #'p) (free-identifier=? #'p #'_))
          #'(begin e e* ...)]

        [(_ v p e e* ...) (identifier? #'p)
          #'(let ([p v]) e e* ...)]

        [(_ v (re record-type clause* ...) e e* ...) (and (identifier? #'re) (free-identifier=? #'re #'record))
          #`(let ([rtd (record-type-descriptor record-type)])
              (when ((record-predicate rtd) v)
                (let ([xs (record-type-field-names rtd)])
                  #,(let loop ([clauses #'(clause* ...)])
                      (syntax-case clauses ()
                        [() #'(begin e e* ...)]
                        [([k p] _ ...)
                          #`(let ([idx (do ([i 0 (add1 i)]) ((or (>= i (vector-length xs)) (symbol=? 'k (vector-ref xs i))) (and (< i (vector-length xs)) i)))])
                              (if idx
                                  (when-match ((record-accessor rtd idx) v) p #,(loop (cdr clauses)))
                                  #,(cond [(syntax->annotation #'k) =>
                                            (lambda (ann)
                                              (let-values ([(file line column) (locate-source-object-source (annotation-source ann) #t #f)])
                                                #`(assertion-violationf 'match "unknown field ~s for record type ~s in ~s on line ~s, character ~s" 'k (record-type-name rtd) #,file #,line #,column)))]
                                          [else #'(assertion-violationf 'match "unknown field ~s for record type ~s" 'k (record-type-name rtd))])))]
                        [(k ks/vs ...) (loop #'([k k] ks/vs ...))])))))]

        [(_ v (ht clause* ...) e e* ...) (and (identifier? #'ht) (free-identifier=? #'ht #'hashtable))
          #`(when (symbol-hashtable? v)
              #,(let loop ([clauses #'(clause* ...)])
                  (syntax-case clauses ()
                    [() #'(begin e e* ...)]
                    [([k p] _ ...) #`(cond [(symbol-hashtable-ref-cell v 'k) => (lambda (k/v) (when-match (cdr k/v) p #,(loop (cdr clauses))))])]
                    [(k ks/vs ...) (loop #'([k k] ks/vs ...))])))]

        [(_ v0 (p f y) e e* ...)
          #'(let ([p v0]) (when-match f y e e* ...))]

        [(_ v `,p e e* ...)
          #'(when-match v p e e* ...)]

        [(_ v `(,@p) e e* ...)
          #'(when (or (pair? v) (null? v)) (when-match v p e e* ...))]

        [(_ v `(p0 . p1) e e* ...)
          #'(when (pair? v) (when-match (car v) `p0 (when-match (cdr v) `p1 e e* ...)))]

        [(_ v p e e* ...)
          #'(when (equal? v p) e e* ...)]))

    (define-syntax (match code)
      (syntax-case code ()
        [(_ v [p e e* ...] ...)
          #`(let ([v0 v])
              (call/1cc
                (lambda (k)
                  (when-match v0 p (call-with-values (lambda () e e* ...) k)) ...
                  #,(cond [(syntax->annotation code) =>
                            (lambda (ann)
                              (let-values ([(file line column) (locate-source-object-source (annotation-source ann) #t #f)])
                                #`(assertion-violationf 'match "unmatched value ~s in ~s on line ~s, character ~s" v0 #,file #,line #,column)))]
                          [else #'(assertion-violationf 'match "unmatched value ~s" v0)]))))])))

  (module (variable-binder make-variable-binder)
    (define-record-type corefn)

    (define-record-type variable-binder
      [parent corefn]
      [fields identifier]
      [protocol (lambda (new)
                  (lambda (identifier)
                    (assert (symbol? identifier))
                    ((new) identifier)))])

    (record-writer
      (record-type-descriptor corefn)
      (lambda (r p wr)
        (display "#<" p)
        (display (record-type-name (record-rtd r)) p)
        (let ([field-names (record-type-field-names (record-rtd r))])
          (do ([i 0 (fx+ i 1)])
              ((fx>= i (vector-length field-names)))
            (display " [" p)
            (display (vector-ref field-names i) p)
            (put-char p #\space)
            (wr ((record-accessor (record-rtd r) i) r) p)
            (put-char p #\])))
        (put-char p #\>))))

  ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Binders.hs#L11-L34
  (define (json-corefn-binder->scheme-corefn corefn)
    (match corefn
      [(hashtable [binderType "VarBinder"] identifier)
        (make-variable-binder (string->symbol identifier))]

      [(hashtable [binderType "NullBinder"])
        '_]

      ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/Literals.hs#L12-L41
      [(hashtable [binderType "LiteralBinder"] [literal (hashtable value literalType)])
        (case literalType
          ["ArrayLiteral" `(array ,@(vector->list (vector-map json-corefn-binder->scheme-corefn value)))]
          ["ObjectLiteral" `(object ,@(vector->list (vector-map (lambda (corefn) (list (vector-ref corefn 0) (json-corefn-binder->scheme-corefn (vector-ref corefn 1)))) value)))]
          ["CharLiteral" (string-ref value 0)]
          ["NumericLiteral" (if (fixnum? value) (fixnum->flonum value) value)]
          [else value])]

      [(hashtable [binderType "ConstructorBinder"] binders [constructorName (hashtable moduleName identifier)])
        `(data ,(vector->list moduleName) ,identifier ,@(vector->list (vector-map json-corefn-binder->scheme-corefn binders)))]

      [(hashtable [binderType "NamedBinder"] identifier binder)
        `(named ,identifier ,(json-corefn-binder->scheme-corefn binder))]))

  (define (json-corefn-expression->scheme-corefn corefn)
    (let ([type (assert (symbol-hashtable-ref corefn 'type #f))])
      (case (string (string-ref type 0) (string-ref type 1))
        ["Va" (let ([value (assert (symbol-hashtable-ref corefn 'value #f))]
                    [sourceSpan (assert (symbol-hashtable-ref (assert (symbol-hashtable-ref corefn 'annotation #f)) 'sourceSpan #f))])
                (let ([moduleName (symbol-hashtable-ref value 'moduleName #f)]
                      [sourcePos (symbol-hashtable-ref value 'sourcePos #f)]
                      [sourceStart (assert (symbol-hashtable-ref sourceSpan 'start #f))]
                      [sourceEnd (assert (symbol-hashtable-ref sourceSpan 'end #f))])
                  `(variable
                    ,(if (and (not (equal? sourceStart '#(0 0))) (not (equal? sourceEnd '#(0 0))) (or moduleName (and sourcePos (not (equal? sourcePos '#(0 0))))))
                      `(,@(vector->list sourceStart) ,@(vector->list sourceEnd))
                      #f)
                    ,(if moduleName (vector->list moduleName) '())
                    ,(assert (symbol-hashtable-ref value 'identifier #f)))))]
        ["Li" (let ([value (assert (symbol-hashtable-ref corefn 'value #f))])
                (let ([literalType (assert (symbol-hashtable-ref value 'literalType #f))]
                      [value (assert (symbol-hashtable-ref value 'value #f))])
                  (case (string-ref literalType 0)
                    [#\C (string-ref value 0)]
                    [#\A `(array ,@(vector->list (vector-map json-corefn-expression->scheme-corefn value)))]
                    [#\O `(object ,@(vector->list (vector-map (lambda (corefn) (list (vector-ref corefn 0) (json-corefn-expression->scheme-corefn (vector-ref corefn 1)))) value)))]
                    [#\N (if (fixnum? value) (fixnum->flonum value) value)]
                    [else value])))]
        ["Co" `(data
                ,(assert (symbol-hashtable-ref corefn 'constructorName #f))
                ,@(vector->list (assert (symbol-hashtable-ref corefn 'fieldNames #f))))]
        ["Ac" `(access
                ,(json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'expression #f)))
                ,(assert (symbol-hashtable-ref corefn 'fieldName #f)))]
        ["Ob" `(update
                ,(json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'expression #f)))
                ,(vector->list (vector-map (lambda (corefn) (list (vector-ref corefn 0) (json-corefn-expression->scheme-corefn (vector-ref corefn 1)))) (assert (symbol-hashtable-ref corefn 'updates #f)))))]
        ["Ab" `(abstraction
                ,(assert (symbol-hashtable-ref corefn 'argument #f))
                ,(json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'body #f))))]
        ["Ap" (let ([sourceSpan (assert (symbol-hashtable-ref (assert (symbol-hashtable-ref corefn 'annotation #f)) 'sourceSpan #f))])
                (let ([sourceStart (assert (symbol-hashtable-ref sourceSpan 'start #f))]
                      [sourceEnd (assert (symbol-hashtable-ref sourceSpan 'end #f))])
                  `(application
                    ,(if (and (not (equal? sourceStart '#(0 0))) (not (equal? sourceEnd '#(0 0))))
                      `(,@(vector->list sourceStart) ,@(vector->list sourceEnd))
                      #f)
                    ,(json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'abstraction #f)))
                    ,(json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'argument #f))))))]
        ["Ca" `(case
                ,(vector->list (vector-map json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'caseExpressions #f))))
                ,@(vector->list
                    (vector-map
                      (lambda (corefn)
                        (let ([binders (vector->list (vector-map json-corefn-binder->scheme-corefn (assert (symbol-hashtable-ref corefn 'binders #f))))])
                          (if (cdr (assert (symbol-hashtable-ref-cell corefn 'isGuarded)))
                              (list binders #t
                                (vector->list
                                  (vector-map
                                    (lambda (corefn)
                                      (list
                                        (json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'guard #f)))
                                        (json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'expression #f)))))
                                    (assert (symbol-hashtable-ref corefn 'expressions #f)))))
                              (list binders #f (json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'expression #f)))))))
                      (assert (symbol-hashtable-ref corefn 'caseAlternatives #f)))))]
        ["Le" (let loop ([binds (vector->list (assert (symbol-hashtable-ref corefn 'binds #f)))])
                (if (null? binds)
                    (json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref corefn 'expression #f)))
                    (if (char=? (string-ref (assert (symbol-hashtable-ref (car binds) 'bindType #f)) 0) #\N)
                        `(bind
                          ,(assert (symbol-hashtable-ref (car binds) 'identifier #f))
                          ,(json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref (car binds) 'expression #f)))
                          ,(loop (cdr binds)))
                        `(bindrec
                          ,(vector->list
                            (vector-map
                              (lambda (bind)
                                (list (assert (symbol-hashtable-ref bind 'identifier #f))
                                      (json-corefn-expression->scheme-corefn (assert (symbol-hashtable-ref bind 'expression #f)))))
                              (assert (symbol-hashtable-ref (car binds) 'binds #f))))
                          ,(loop (cdr binds))))))])))

  (define (json-corefn->scheme-corefn corefn)
    (let ([re-exports (hashtable-map-values vector->list (assert (symbol-hashtable-ref corefn 'reExports #f)))]
          [module-path (assert (symbol-hashtable-ref corefn 'modulePath #f))]
          [module-name (vector->list (assert (symbol-hashtable-ref corefn 'moduleName #f)))]
          [foreign-imports (vector->list (assert (symbol-hashtable-ref corefn 'foreign #f)))]
          [exports (vector->list (assert (symbol-hashtable-ref corefn 'exports #f)))]
          [declarations (let loop ([decls (vector->list (assert (symbol-hashtable-ref corefn 'decls #f)))] [acc '()])
                          (if (null? decls)
                              (reverse acc)
                              (let ([bind-type (symbol-hashtable-ref (car decls) 'bindType #f)])
                                (if (and bind-type (string=? bind-type "Rec"))
                                    (loop (append (vector->list (assert (symbol-hashtable-ref (car decls) 'binds #f))) (cdr decls)) acc)
                                    (let ([expression (assert (symbol-hashtable-ref (car decls) 'expression #f))])
                                      (loop (cdr decls)
                                        (let ([meta-ann (assert (symbol-hashtable-ref (assert (symbol-hashtable-ref expression 'annotation #f)) 'meta #f))]
                                              [id (assert (symbol-hashtable-ref (car decls) 'identifier #f))])
                                          (let ([meta-type (and (not (eq? meta-ann 'null)) (symbol-hashtable-ref meta-ann 'metaType #f))])
                                            (case meta-type
                                              ["IsNewtype"
                                                (cons (list id '(newtype))
                                                      acc)]
                                              [else (cons (list id (json-corefn-expression->scheme-corefn expression)) acc)])))))))))])
      (let ([imports (filter (lambda (x) (and (not (equal? x '("Prim"))) (not (equal? x module-name)))) (vector->list (vector-map (lambda (x) (vector->list (assert (symbol-hashtable-ref x 'moduleName #f)))) (assert (symbol-hashtable-ref corefn 'imports #f)))))])
        `(corefn-module
          ,module-name
          ,module-path
          ,imports
          ,foreign-imports
          ,exports
          ,re-exports
          ,declarations))))

  (define (module-name->prefix module-name)
    (call-with-string-output-port (lambda (sop) (for-each (lambda (s) (put-string sop s) (put-char sop #\.)) module-name))))

  (define (module-name->dotted module-name)
    (call-with-string-output-port
      (lambda (sop)
        (put-string sop (car module-name))
        (for-each (lambda (s) (put-char sop #\.) (put-string sop s)) (cdr module-name)))))

  (define (corefn-case-binding->scheme corefn)
    (match corefn
      [(record variable-binder identifier)
        identifier]

      [`(object ,@k/v*)
          `(object ,@(map (lambda (k/v) (list (car k/v) (corefn-case-binding->scheme (cadr k/v)))) k/v*))]
      [`(array ,@xs)
          `(array ,@(map corefn-case-binding->scheme xs))]
      [`(named ,(x (string->symbol x) x) ,p)
          `(,x ,(corefn-case-binding->scheme p))]
      [`(data ,(module-prefix (module-name->prefix module-prefix) module-prefix) ,name ,@args)
          `(data ,(string->symbol (string-append module-prefix name))
            ,@(map corefn-case-binding->scheme args))]
      [else (assert (atom? corefn)) corefn]))

  (define (function-declaration->scheme module-prefix corefn)
    `(define
      ,(string->symbol (string-append module-prefix (car corefn)))
      ,(let loop ([corefn (cadr corefn)])
        (match corefn
          [`(variable ,source-location ,(xs (module-name->prefix xs) module-prefix) ,identifier)
              (list '%ref 'src source-location (string->symbol (string-append module-prefix identifier)))]
          [`(application ,source-location ,abstraction ,expression)
              (list '%app 'src source-location (loop abstraction) (loop expression))]
          [`(abstraction ,(x (string->symbol x) x) ,body) `(-> ,x ,(loop body))]
          [`(bind ,(x (string->symbol x) x) ,e ,body)
              (let inner-loop ([body body] [acc (list (list x (loop e)))])
                (match body
                  [`(bind ,(x (string->symbol x) x) ,e ,body) (inner-loop body (cons (list x (loop e)) acc))]
                  [else `(,(if (= (length acc) 1) 'let 'let*) ,(reverse acc) ,(loop body))]))]
          [`(bindrec ,bindings ,body)
              `(letrec
                (,@(map (lambda (var/val) (list (string->symbol (car var/val)) (loop (cadr var/val)))) bindings))
                ,(loop body))]
          [`(case ,e* ,@clause*)
              `(case ,(map loop e*)
                  ,@(map
                      (lambda (clause)
                        (match clause
                          [`(,ps #f ,e) `(,(map corefn-case-binding->scheme ps) -> ,(loop e))]
                          [`(,ps #t ,es) `(,(map corefn-case-binding->scheme ps) ,@(map (lambda (e) `(,(loop (car e)) -> ,(loop (cadr e)))) es))]
                          [else (assert #f)]))
                      clause*))]
          [`(object ,@k/v*)
              `(object ,@(map (lambda (k/v) (list (car k/v) (loop (cadr k/v)))) k/v*))]
          [`(array ,@xs)
              `(array ,@(map loop xs))]
          [`(update ,e ,k/v*)
              `(update ,(loop e) ,@(map (lambda (k/v) (list (car k/v) (loop (cadr k/v)))) k/v*))]
          [`(access ,e ,k)
              `(access ,(loop e) ,k)]
          [else (assert (atom? corefn)) corefn]))))

  (define (data-declaration->scheme module-prefix corefn)
    (let ([name (string->symbol (string-append module-prefix (car corefn)))]
          [arg-names (cddadr corefn)])
      `(define-data-constructor ,name ,(length arg-names))))

  (define (newtype-declaration->scheme module-prefix corefn)
    (let ([name (string->symbol (string-append module-prefix (car corefn)))])
      `(define-newtype-constructor ,name)))

  (define (corefn->library corefn)
    (let ([corefn (json-corefn->scheme-corefn corefn)])
      (let-values ([(module-name module-path imports foreign-imports exports re-exports declarations) (apply values (cdr corefn))])
        (let ([module-prefix (module-name->prefix module-name)])
          (let*-values ([(data-declarations declarations) (partition (lambda (item) (match item [`(,name (data ,@_)) #t] [else #f])) declarations)]
                        [(newtype-declarations declarations) (partition (lambda (item) (match item [`(,name (newtype)) #t] [else #f])) declarations)])
            `(library (,(string->symbol (module-name->dotted module-name)))
                (export
                  ,@(map (lambda (export) (string->symbol (string-append module-prefix export))) (sort string<? exports))
                  ,@(let-values ([(ks vss) (hashtable-entries re-exports)])
                      (let ([vs (vector-map (lambda (k vs) (let ([k (symbol->string k)]) (map (lambda (v) (string->symbol (string-append k "." v))) vs))) ks vss)])
                        (do ([i 0 (add1 i)] [acc '() (append (vector-ref vs i) acc)]) ((>= i (vector-length vs)) acc)))))
                ,@(if (pair? foreign-imports)
                    `((import (only (chezscheme) import module include))
                      (module foreign-module ,(map string->symbol foreign-imports)
                        (include ,(string-append (path-root module-path) ".scm")))
                      (import (prefix foreign-module ,(string->symbol module-prefix))))
                    '())
                (import (only (chezscheme) define let let* letrec define-syntax make-compile-time-value)
                        (only (prim) %app %ref -> define-newtype-constructor define-data-constructor case object array data access update)
                        ,@(map (lambda (x) (list (string->symbol x))) (sort string<? (map module-name->dotted imports))))
                (define-syntax src (make-compile-time-value ,module-path))
                ,@(map
                    (lambda (x) (newtype-declaration->scheme module-prefix x))
                    (sort (lambda (x y) (string<? (car x) (car y))) newtype-declarations))
                ,@(map
                    (lambda (x) (data-declaration->scheme module-prefix x))
                    (sort (lambda (x y) (string<? (car x) (car y))) data-declarations))
                ,@(map
                    (lambda (x) (function-declaration->scheme module-prefix x))
                    declarations)))))))

  (define (put-corefn-library corefn-library textual-output-port)
    (let ([case-fmt  (pretty-format 'case)]
          [array-fmt (pretty-format 'array)])
      (pretty-format '%app   '(_ var (alt (bracket e ...) e) 5 e 5 e))
      (pretty-format '%ref   '(_ var (alt (bracket e ...) e) e))
      (pretty-format '->     '(_ var body))
      (pretty-format 'object '(_ [bracket x e] 7 ...))
      (pretty-format 'update '(_ _ [bracket x e] 7 ...))
      (pretty-format 'array  '(_ e 6 ...))
      (pretty-format 'case   '(_ (_ ...) 1 (alt [bracket (_ ...) '-> _]
                                                [bracket (_ ...) 1 [bracket _ '-> _] ...]) ...))
      (let-values ([(name exports core-import foreign-module foreign-import import0 imports src definitions)
                      (match corefn-library
                        [`(library ,name (export ,@exports) (import ,@core-import) (module ,@foreign-module) (import ,@foreign-import) (import ,import0 ,@imports) ,src ,@definitions)
                            (values name exports (cons 'import core-import) (cons 'module foreign-module) (cons 'import foreign-import) import0 imports src definitions)]
                        [`(library ,name (export ,@exports) (import ,import0 ,@imports) ,src ,@definitions)
                            (values name exports #f #f #f import0 imports src definitions)])])
        (put-string textual-output-port "#!chezscheme\n\n(library ")
        (put-datum textual-output-port name)
        (put-char textual-output-port #\newline)
        (match exports
          ['() (put-string textual-output-port "  (export)")]
          [`(,x ,@xs)
              (put-string textual-output-port "  (export ")
              (put-datum textual-output-port x)
              (for-each
                (lambda (x)
                  (put-char textual-output-port #\newline)
                  (do ([i 0 (add1 i)]) ((fx>= i 10))
                    (put-char textual-output-port #\space))
                  (put-datum textual-output-port x))
                xs)
              (put-char textual-output-port #\))])
        (when (and core-import foreign-module foreign-import)
          (put-string textual-output-port "\n\n  ")
          (put-datum textual-output-port core-import)
          (put-string textual-output-port "\n  ")
          (put-datum textual-output-port foreign-module)
          (put-string textual-output-port "\n  ")
          (put-datum textual-output-port foreign-import))
        (put-string textual-output-port "\n\n  (import ")
        (put-datum textual-output-port import0)
        (for-each
          (lambda (import)
            (put-char textual-output-port #\newline)
            (do ([i 0 (add1 i)]) ((fx>= i 10))
              (put-char textual-output-port #\space))
            (put-datum textual-output-port import))
          imports)
        (put-char textual-output-port #\))
        (format textual-output-port "\n\n  ~s" src)
        (parameterize ([pretty-initial-indent 4])
          (for-each
            (lambda (item)
              (match item
                [`(define ,x ,e)
                    (format textual-output-port "\n\n  (define ~s\n    " x)
                    (let ([s (call-with-string-output-port (lambda (sop) (pretty-print e sop)))])
                      (put-string textual-output-port s 0 (sub1 (string-length s))))
                    (put-char textual-output-port #\))]
                [`(define-data-constructor ,x ,arg-length)
                  (format textual-output-port "\n\n  (define-data-constructor ~s ~s)" x arg-length)]
                [`(define-newtype-constructor ,x)
                  (format textual-output-port "\n\n  (define-newtype-constructor ~s)" x)]
                [else (assert #f)]))
            definitions))
        (put-char textual-output-port #\))
        (put-char textual-output-port #\newline))
      (pretty-format 'case  case-fmt)
      (pretty-format 'array array-fmt)))

  (define (transpile-corefn-output-folder path)
    (for-each
      (lambda (dir)
        (let ([path (string-append path "/" dir)])
          (when (file-directory? path)
            (let ([corefn (call-with-input-file (string-append path "/corefn.json") read-json)])
              (call-with-output-file (string-append path ".scm")
                (lambda (textual-output-port) (put-corefn-library (corefn->library corefn) textual-output-port))
                '(truncate))))))
      (directory-list path))))
