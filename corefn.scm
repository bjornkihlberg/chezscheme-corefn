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

  (module (variable-binder
           make-variable-binder
           null-binder
           make-null-binder
           named-binder
           make-named-binder
           newtype-binder
           make-newtype-binder
           data-binder
           make-data-binder
           array-binder
           make-array-binder
           object-binder
           make-object-binder
           atomic-binder
           make-atomic-binder
           source-location
           make-source-location
           source-location-start-line
           source-location-start-char
           source-location-end-line
           source-location-end-char
           variable-expression
           make-variable-expression
           data-expression
           make-data-expression
           access-expression
           make-access-expression
           update-expression
           make-update-expression
           abstraction-expression
           make-abstraction-expression
           atomic-expression
           make-atomic-expression
           array-expression
           make-array-expression
           object-expression
           make-object-expression
           application-expression
           make-application-expression
           bind-expression
           make-bind-expression
           recursive-bind-expression
           make-recursive-bind-expression
           case-expression
           make-case-expression
           case-alternative
           make-case-alternative)

    (define-record-type corefn)

    (define (binder? e)
      (and
        (corefn? e)
        (or (variable-binder? e)
            (null-binder? e)
            (named-binder? e)
            (newtype-binder? e)
            (data-binder? e)
            (array-binder? e)
            (object-binder? e)
            (atomic-binder? e))))

    (define (expression? e)
      (and
        (corefn? e)
        (or (case-expression? e)
            (recursive-bind-expression? e)
            (bind-expression? e)
            (application-expression? e)
            (object-expression? e)
            (array-expression? e)
            (atomic-expression? e)
            (abstraction-expression? e)
            (update-expression? e)
            (access-expression? e)
            (data-expression? e)
            (variable-expression? e))))

    (define-record-type source-location
      [fields start-line start-char end-line end-char]
      [protocol (lambda (new)
                  (lambda (start-line start-char end-line end-char)
                    (assert (fixnum? start-line))
                    (assert (fxpositive? start-line))
                    (assert (fixnum? start-char))
                    (assert (fxpositive? start-char))
                    (assert (fixnum? end-line))
                    (assert (fxpositive? end-line))
                    (assert (fixnum? end-char))
                    (assert (fxpositive? end-char))
                    (new start-line start-char end-line end-char)))]
      [opaque #t])

    (define-record-type case-alternative
      [parent corefn]
      [fields binders expression]
      [protocol (lambda (new)
                  (lambda (binders expression)
                    (assert (vector? binders))
                    (assert (fxpositive? (vector-length binders)))
                    (vector-for-each (lambda (binder) (assert (binder? binder))) binders)
                    (if (vector? expression)
                        (vector-for-each
                          (lambda (expression)
                            (assert (pair? expression))
                            (assert (expression? (car expression)))
                            (assert (expression? (cdr expression))))
                          expression)
                        (assert (expression? expression)))
                    ((new) binders expression)))])

    (define-record-type case-expression
      [parent corefn]
      [fields expressions alternatives]
      [protocol (lambda (new)
                  (lambda (expressions alternatives)
                    (assert (vector? expressions))
                    (assert (fxpositive? (vector-length expressions)))
                    (vector-for-each
                      (lambda (expression) (assert (expression? expression)))
                      expressions)
                    (assert (vector? alternatives))
                    (assert (fxpositive? (vector-length alternatives)))
                    (vector-for-each
                      (lambda (alternative)
                        (assert (case-alternative? alternative))
                        (assert (= (vector-length (case-alternative-binders alternative)) (vector-length expressions))))
                      alternatives)
                    ((new) expressions alternatives)))])

    (define-record-type recursive-bind-expression
      [parent corefn]
      [fields bindings body]
      [protocol (lambda (new)
                  (lambda (bindings body)
                    (assert (vector? bindings))
                    (vector-for-each
                      (lambda (binding)
                        (assert (pair? binding))
                        (assert (symbol? (car binding)))
                        (assert (expression? (cdr binding))))
                      bindings)
                    (assert (expression? body))
                    ((new) bindings body)))])

    (define-record-type bind-expression
      [parent corefn]
      [fields identifier value body]
      [protocol (lambda (new)
                  (lambda (identifier value body)
                    (assert (symbol? identifier))
                    (assert (expression? body))
                    ((new) identifier value body)))])

    (define-record-type application-expression
      [parent corefn]
      [fields source-location abstraction value]
      [protocol (lambda (new)
                  (lambda (source-location abstraction value)
                    (when source-location (assert (source-location? source-location)))
                    (assert (expression? abstraction))
                    (assert (expression? value))
                    ((new) source-location abstraction value)))])

    (define-record-type object-expression
      [parent corefn]
      [fields items]
      [protocol (lambda (new)
                  (lambda (items)
                    (assert (vector? items))
                    (vector-for-each
                      (lambda (item)
                        (assert (pair? item))
                        (assert (string? (car item)))
                        (assert (expression? (cdr item))))
                      items)
                    ((new) items)))])

    (define-record-type array-expression
      [parent corefn]
      [fields items]
      [protocol (lambda (new)
                  (lambda (items)
                    (assert (vector? items))
                    (vector-for-each
                      (lambda (item) (assert (expression? item)))
                      items)
                    ((new) items)))])

    (define-record-type atomic-expression
      [parent corefn]
      [fields atom]
      [protocol (lambda (new)
                  (lambda (atom)
                    (assert (or (char? atom)
                                (boolean? atom)
                                (string? atom)
                                (and (integer? atom) (exact? atom))
                                (and (number? atom) (inexact? atom))))
                    ((new) atom)))])

    (define-record-type abstraction-expression
      [parent corefn]
      [fields argument body]
      [protocol (lambda (new)
                  (lambda (argument body)
                    (assert (symbol? argument))
                    (assert (expression? body))
                    ((new) argument body)))])

    (define-record-type update-expression
      [parent corefn]
      [fields object updates]
      [protocol (lambda (new)
                  (lambda (object updates)
                    (assert (expression? object))
                    (assert (vector? updates))
                    (vector-for-each
                      (lambda (k/v)
                        (assert (pair? k/v))
                        (assert (string? (car k/v)))
                        (assert (expression? (cdr k/v))))
                      updates)
                    ((new) object updates)))])

    (define-record-type access-expression
      [parent corefn]
      [fields object field-name]
      [protocol (lambda (new)
                  (lambda (object field-name)
                    (assert (expression? object))
                    (assert (string? field-name))
                    ((new) object field-name)))])

    (define-record-type data-expression
      [parent corefn]
      [fields constructor-name field-count]
      [protocol (lambda (new)
                  (lambda (constructor-name field-count)
                    (assert (symbol? constructor-name))
                    (assert (fixnum? field-count))
                    (assert (fxnonnegative? field-count))
                    ((new) constructor-name field-count)))])

    (define-record-type variable-expression
      [parent corefn]
      [fields module-name source-location identifier]
      [protocol (lambda (new)
                  (lambda (module-name source-location identifier)
                    (assert (vector? module-name))
                    (vector-for-each (lambda (s) (assert (symbol? s))) module-name)
                    (when source-location (assert (source-location? source-location)))
                    (assert (symbol? identifier))
                    ((new) module-name source-location identifier)))])

    (define-record-type variable-binder
      [parent corefn]
      [fields identifier]
      [protocol (lambda (new)
                  (lambda (identifier)
                    (assert (symbol? identifier))
                    ((new) identifier)))])

    (define-record-type null-binder
      [parent corefn])

    (define-record-type named-binder
      [parent corefn]
      [fields identifier binder]
      [protocol (lambda (new)
                  (lambda (identifier binder)
                    (assert (symbol? identifier))
                    (assert (binder? binder))
                    ((new) identifier binder)))])

    (define-record-type newtype-binder
      [parent corefn]
      [fields binder]
      [protocol (lambda (new)
                  (lambda (binder)
                    (assert (binder? binder))
                    ((new) binder)))])

    (define-record-type data-binder
      [parent corefn]
      [fields module-name identifier binders]
      [protocol (lambda (new)
                  (lambda (module-name identifier binders)
                    (assert (vector? module-name))
                    (vector-for-each (lambda (s) (assert (symbol? s))) module-name)
                    (assert (symbol? identifier))
                    (assert (vector? binders))
                    (vector-for-each (lambda (binder) (assert (binder? binder))) binders)
                    ((new) module-name identifier binders)))])

    (define-record-type array-binder
      [parent corefn]
      [fields binders]
      [protocol (lambda (new)
                  (lambda (binders)
                    (assert (vector? binders))
                    (vector-for-each (lambda (binder) (assert (binder? binder))) binders)
                    ((new) binders)))])

    (define-record-type object-binder
      [parent corefn]
      [fields binders]
      [protocol (lambda (new)
                  (lambda (binders)
                    (assert (vector? binders))
                    (vector-for-each
                      (lambda (binder)
                        (assert (pair? binder))
                        (assert (string? (car binder)))
                        (assert (binder? (cdr binder))))
                      binders)
                    ((new) binders)))])

    (define-record-type atomic-binder
      [parent corefn]
      [fields atom]
      [protocol (lambda (new)
                  (lambda (atom)
                    (assert (or (char? atom)
                                (boolean? atom)
                                (string? atom)
                                (and (integer? atom) (exact? atom))
                                (and (number? atom) (inexact? atom))))
                    ((new) atom)))])

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
        (make-null-binder)]

      ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/Literals.hs#L12-L41
      ; https://github.com/purescript/purescript/blob/fc3fa8897916de1a3973de976eaea1fba23b4df9/src/Language/PureScript/CoreFn/ToJSON.hs#L61-L96
      [(hashtable [binderType "LiteralBinder"] [literal (hashtable value literalType)])
        (case literalType
          ["ArrayLiteral"
            (make-array-binder (vector-map json-corefn-binder->scheme-corefn value))]

          ["ObjectLiteral"
            (make-object-binder (vector-map (lambda (kv) (cons (vector-ref kv 0) (json-corefn-binder->scheme-corefn (vector-ref kv 1)))) value))]

          ["CharLiteral"
            (make-atomic-binder (string-ref value 0))]

          ["NumberLiteral"
            (make-atomic-binder (exact->inexact value))]

          [else
            (make-atomic-binder value)])]

      [(hashtable [binderType "ConstructorBinder"] binders [constructorName (hashtable moduleName identifier)] [annotation (hashtable meta)])
        ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Ann.hs#L9-L12
        ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Meta.hs#L10-L38
        (match meta
          [(hashtable [metaType "IsNewtype"])
            (assert (= (vector-length binders) 1))
            (make-newtype-binder (json-corefn-binder->scheme-corefn (vector-ref binders 0)))]

          [(hashtable [metaType "IsConstructor"])
            (make-data-binder (vector-map string->symbol moduleName) (string->symbol identifier) (vector-map json-corefn-binder->scheme-corefn binders))])]

      [(hashtable [binderType "NamedBinder"] identifier binder)
        (make-named-binder (string->symbol identifier) (json-corefn-binder->scheme-corefn binder))]))

  ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Expr.hs#L15-L55
  (define (json-corefn-expression->scheme-corefn corefn)
    (match corefn
      ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/SourcePos.hs#L49-L56
      ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/SourcePos.hs#L75-L80
      [(hashtable [type "Var"] value [annotation (hashtable [sourceSpan (hashtable start end)])])
        (let ([moduleName (symbol-hashtable-ref value 'moduleName #f)]
              ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/SourcePos.hs#L22-L28
              ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/SourcePos.hs#L40-L42
              [sourcePos (symbol-hashtable-ref value 'sourcePos #f)])
          (make-variable-expression
            (if moduleName (vector-map string->symbol moduleName) '#())
            (and
              (not (equal? start '#(0 0)))
              (or moduleName (and sourcePos (not (equal? sourcePos '#(0 0)))))
              (make-source-location (vector-ref start 0) (vector-ref start 1) (vector-ref end 0) (vector-ref end 1)))
            (string->symbol (assert (symbol-hashtable-ref value 'identifier #f)))))]

      ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/AST/Literals.hs#L12-L41
      ; https://github.com/purescript/purescript/blob/fc3fa8897916de1a3973de976eaea1fba23b4df9/src/Language/PureScript/CoreFn/ToJSON.hs#L61-L96
      [(hashtable [type "Literal"] [value (hashtable literalType value)])
        (case literalType
          ["CharLiteral"
            (make-atomic-expression (string-ref value 0))]

          ["ArrayLiteral"
            (make-array-expression (vector-map json-corefn-expression->scheme-corefn value))]

          ["ObjectLiteral"
            (make-object-expression (vector-map (lambda (corefn) (cons (vector-ref corefn 0) (json-corefn-expression->scheme-corefn (vector-ref corefn 1)))) value))]

          ["NumberLiteral"
            (make-atomic-expression (exact->inexact value))]

          [else
            (make-atomic-expression value)])]

      [(hashtable [type "Constructor"] constructorName fieldNames)
        (make-data-expression (string->symbol constructorName) (vector-length fieldNames))]

      [(hashtable [type "Accessor"] expression fieldName)
        (make-access-expression (json-corefn-expression->scheme-corefn expression) fieldName)]

      [(hashtable [type "ObjectUpdate"] expression updates)
        (make-update-expression
          (json-corefn-expression->scheme-corefn expression)
          (vector-map (lambda (kv) (cons (vector-ref kv 0) (json-corefn-expression->scheme-corefn (vector-ref kv 1)))) updates))]

      [(hashtable [type "Abs"] argument body)
        (make-abstraction-expression (string->symbol argument) (json-corefn-expression->scheme-corefn body))]

      [(hashtable [type "App"] [annotation (hashtable [sourceSpan (hashtable start end)])] abstraction argument)
        (make-application-expression
          (and
            (not (equal? start '#(0 0)))
            (make-source-location (vector-ref start 0) (vector-ref start 1) (vector-ref end 0) (vector-ref end 1)))
          (json-corefn-expression->scheme-corefn abstraction)
          (json-corefn-expression->scheme-corefn argument))]

      [(hashtable [type "Case"] caseExpressions caseAlternatives)
        (make-case-expression
          (vector-map json-corefn-expression->scheme-corefn caseExpressions)
          (vector-map (lambda (caseAlternative)
                        ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Expr.hs#L75-L87
                        ; https://github.com/purescript/purescript/blob/fc3fa8897916de1a3973de976eaea1fba23b4df9/src/Language/PureScript/CoreFn/ToJSON.hs#L214-L224
                        (let ([binders (vector-map json-corefn-binder->scheme-corefn (assert (symbol-hashtable-ref caseAlternative 'binders #f)))])
                          (match caseAlternative
                            ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Expr.hs#L70-L73
                            [(hashtable [isGuarded #t] expressions)
                              (make-case-alternative binders
                                (vector-map (lambda (expression)
                                              (match expression
                                                [(hashtable guard expression)
                                                  (cons (json-corefn-expression->scheme-corefn guard)
                                                        (json-corefn-expression->scheme-corefn expression))]))
                                            expressions))]

                            [(hashtable [isGuarded #f] expression)
                              (make-case-alternative binders (json-corefn-expression->scheme-corefn expression))])))
                      caseAlternatives))]

      [(hashtable [type "Let"] binds expression)
        (let loop ([items (vector->list binds)])
          (if (null? items)
              (json-corefn-expression->scheme-corefn expression)
              ; https://github.com/purescript/purescript/blob/master/src/Language/PureScript/CoreFn/Expr.hs#L57-L68
              ; https://github.com/purescript/purescript/blob/fc3fa8897916de1a3973de976eaea1fba23b4df9/src/Language/PureScript/CoreFn/ToJSON.hs#L142-L159
              (match (car items)
                [(hashtable [bindType "NonRec"] identifier expression)
                  (make-bind-expression
                    (string->symbol identifier)
                    (json-corefn-expression->scheme-corefn expression)
                    (loop (cdr items)))]

                [(hashtable [bindType "Rec"] binds)
                  (make-recursive-bind-expression
                    (vector-map (lambda (bind)
                                  (match bind
                                    [(hashtable identifier expression)
                                      (cons (string->symbol identifier) (json-corefn-expression->scheme-corefn expression))]))
                                binds)
                    (loop (cdr items)))])))]))

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

      [(record null-binder)
        '_]

      [(record object-binder binders)
        `(%object ,@(vector->list (vector-map (lambda (k/v) (list (car k/v) (corefn-case-binding->scheme (cdr k/v)))) binders)))]

      [(record array-binder binders)
        `(%array ,@(vector->list (vector-map corefn-case-binding->scheme binders)))]

      [(record named-binder identifier binder)
        (list identifier (corefn-case-binding->scheme binder))]

      [(record data-binder module-name identifier binders)
        `(%data ,(vector->list module-name) ,identifier ,@(vector->list (vector-map corefn-case-binding->scheme binders)))]

      [(record newtype-binder binder)
        (corefn-case-binding->scheme binder)]

      [(record atomic-binder atom)
        atom]))

  (define (function-declaration->scheme module-prefix corefn)
    `(define
      ,(string->symbol (string-append module-prefix (car corefn)))
      ,(let loop ([corefn (cadr corefn)])
        (match corefn
          [(record variable-expression source-location module-name identifier)
            (list '%ref 'src
                  (and
                    source-location
                    (list (source-location-start-line source-location)
                          (source-location-start-char source-location)
                          (source-location-end-line source-location)
                          (source-location-end-char source-location)))
                  (vector->list module-name) identifier)]

          [(record application-expression source-location abstraction value)
            (list '%app 'src
                  (and
                    source-location
                    (list (source-location-start-line source-location)
                          (source-location-start-char source-location)
                          (source-location-end-line source-location)
                          (source-location-end-char source-location)))
                  (loop abstraction)
                  (loop value))]

          [(record abstraction-expression argument body)
            `(-> ,argument ,(loop body))]

          [(record bind-expression identifier value body)
            (let inner-loop ([body body] [acc (list (list identifier (loop value)))])
              (match body
                [(record bind-expression identifier value body)
                  (inner-loop body (cons (list identifier (loop value)) acc))]

                [else
                  (list (if (= (length acc) 1) 'let 'let*) (reverse acc) (loop body))]))]

          [(record recursive-bind-expression bindings body)
            `(letrec ,(vector->list (vector-map (lambda (binding) (list (car binding) (loop (cdr binding)))) bindings)) ,(loop body))]

          [(record case-expression expressions alternatives)
            `(%case
              ,(vector->list (vector-map loop expressions))
              ,@(vector->list
                  (vector-map (lambda (alternative)
                                (match alternative
                                  [(record case-alternative binders expression)
                                    (if (vector? expression)
                                      `(,(vector->list (vector-map corefn-case-binding->scheme binders))
                                        ,@(vector->list
                                            (vector-map (lambda (expression) `(,(loop (car expression)) -> ,(loop (cdr expression))))
                                                        expression)))
                                      `(,(vector->list (vector-map corefn-case-binding->scheme binders)) -> ,(loop expression)))]))
                              alternatives)))]

          [(record object-expression items)
            `(%object ,@(vector->list (vector-map (lambda (k/v) (list (car k/v) (loop (cdr k/v)))) items)))]

          [(record array-expression items)
            `(%array ,@(vector->list (vector-map loop items)))]

          [(record update-expression object updates)
            `(%update ,(loop object) ,@(vector->list (vector-map (lambda (k/v) (list (car k/v) (loop (cdr k/v)))) updates)))]

          [(record access-expression object field-name)
            `(%access ,(loop object) ,field-name)]

          [(record atomic-expression atom)
            atom]))))

  (define (data-declaration->scheme module-prefix corefn)
    (match corefn
      [`(,name ,(record data-expression field-count))
        `(define-data-constructor ,(string->symbol (string-append module-prefix name)) ,field-count)]))

  (define (newtype-declaration->scheme module-prefix corefn)
    (let ([name (string->symbol (string-append module-prefix (car corefn)))])
      `(define-newtype-constructor ,name)))

  (define (corefn->library corefn)
    (let ([corefn (json-corefn->scheme-corefn corefn)])
      (let-values ([(module-name module-path imports foreign-imports exports re-exports declarations) (apply values (cdr corefn))])
        (let ([module-prefix (module-name->prefix module-name)])
          (let*-values ([(data-declarations declarations) (partition (lambda (item) (match item [`(,name ,(record data-expression)) #t] [else #f])) declarations)]
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
                        (only (prim) %app %ref -> define-newtype-constructor define-data-constructor %case %object %array %data %access %update)
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
    (let ([case-fmt  (pretty-format 'case)])
      (pretty-format '%app   '(_ var (alt (bracket e ...) e) 5 e 5 e))
      (pretty-format '%ref   '(_ var (alt (bracket e ...) e) e e))
      (pretty-format '->     '(_ var body))
      (pretty-format '%object '(_ [bracket x e] 8 ...))
      (pretty-format '%update '(_ _ [bracket x e] 8 ...))
      (pretty-format '%array  '(_ e 7 ...))
      (pretty-format '%case   '(_ (_ ...) 1 (alt [bracket (_ ...) '-> _]
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
      (pretty-format 'case  case-fmt)))

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
