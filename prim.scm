#!chezscheme

(library (prim)
  (export %app
          %ref
          ->
          define-newtype-constructor
          define-data-constructor
          %case
          %object
          %array
          %data
          %access
          %update)

  (import (chezscheme))

  (define-syntax ->
    (syntax-rules ()
      [(_ arg body) (lambda (arg) body)]))

  (define identifier-role)

  (define-syntax (define-newtype-constructor code)
    (syntax-case code ()
      [(_ name)
        #'(begin
            (define (name x) (warningf 'name "newtype constructor executed with ~s" x) x)
            (define-property name identifier-role 'newtype))]))

  (define-syntax (define-data-constructor code)
    (syntax-case code ()
      [(_ name n)
        (with-syntax ([(args ...) (generate-temporaries (iota (datum n)))])
          #'(define (name args ...) (vector 'name args ...)))]))

  (meta define (identifier-path module-name name)
    (datum->syntax name
      (string->symbol
        (apply
          string-append
          (reverse
            (cons (symbol->string (syntax->datum name))
                  (fold-left
                    (lambda (acc x) (cons* "." (symbol->string x) acc))
                    '()
                    (syntax->datum module-name))))))))

  (define-syntax %app
    (lambda (code)
      (lambda (lookup)
        (syntax-case code ()
          [(_ _ _ (ref _ _ module-path name) arg)
            (and
              (identifier? #'ref)
              (free-identifier=? #'ref #'%ref)
              (eq? (lookup (identifier-path #'module-path #'name) #'identifier-role) 'newtype))
            #'arg]

          [(_ src span f x)
            #'(f x)]))))

  (define-syntax (%ref code)
    (syntax-case code ()
      [(_ _ _ (p) n) (and (free-identifier=? #'p #'Prim) (free-identifier=? #'n #'undefined))
        #'(void)]

      [(_ src span module-name name) (identifier-path #'module-name #'name)]))

  (define-syntax corefn-case-clause
    (lambda (code)
      (lambda (lookup)
        (syntax-case code (->)
          [(_ () [() -> e])
            #'e]
          [(_ () [() [t -> e] ...])
            #'(cond [t e] ...)]
          [(_ (v vs ...) clause) (pair? (datum v))
            #'(let ([u v]) (corefn-case-clause (u vs ...) clause))]
          [(_ (v vs ...) [(p ps ...) clause* ...]) (and (identifier? #'p) (free-identifier=? #'p #'_))
            #'(corefn-case-clause (vs ...) [(ps ...) clause* ...])]
          [(_ (v vs ...) [(p ps ...) clause* ...]) (identifier? #'p)
            #'(let ([p v]) (corefn-case-clause (vs ...) [(ps ...) clause* ...]))]
          [(_ (v vs ...) [((d module-name name xs ...) ps ...) clause* ...]) (and (identifier? #'d) (free-identifier=? #'d #'%data))
            #`(when (symbol=? (vector-ref v 0) '#,(identifier-path #'module-name #'name))
                (corefn-case-clause
                  (#,@(map (lambda (i) #`(vector-ref v #,(add1 i))) (iota (length #'(xs ...)))) vs ...)
                  ((xs ... ps ...) clause* ...)))]
          [(_ (v vs ...) [((a xs ...) ps ...) clause* ...]) (and (identifier? #'a) (free-identifier=? #'a #'%array))
            (let ([n (length #'(xs ...))])
              #`(when (= (vector-length v) #,n)
                  (corefn-case-clause (#,@(map (lambda (i) #`(vector-ref v #,i)) (iota n)) vs ...)
                    [(xs ... ps ...) clause* ...])))]
          [(_ (v vs ...) [((o) ps ...) clause* ...]) (and (identifier? #'o) (free-identifier=? #'o #'%object))
            #'(corefn-case-clause (vs ...) [(ps ...) clause* ...])]
          [(m (v vs ...) [((o [k x] k/x ...) ps ...) clause* ...]) (and (identifier? #'o) (free-identifier=? #'o #'%object))
            #`(let ([v0 (%access v k)])
                (corefn-case-clause (v0 v vs ...) [(x (o k/x ...) ps ...) clause* ...]))]
          [(_ (v vs ...) [((n p) ps ...) clause* ...]) (identifier? #'n)
            #'(let ([n v]) (corefn-case-clause (v vs ...) [(p ps ...) clause* ...]))]
          [(_ (v vs ...) [(p ps ...) clause* ...])
            #'(when (equal? v p) (corefn-case-clause (vs ...) [(ps ...) clause* ...]))]))))

  (define-syntax (%case code)
    (syntax-case code (->)
      [(_ (vs ...))
        #'(assertion-violationf 'case "No matching clause for ~s" (list vs ...))]
      [(m (v vs ...) clause+ ...)
        (let ([k (datum->syntax #'m (gensym "k"))])
          (let* ([v/u* (map (lambda (v) #`(#,(datum->syntax #'m (gensym)) #,v)) #'(v vs ...))] [u* (map car v/u*)])
            #`(call/1cc (lambda (#,k)
                (let (#,@v/u*)
                  #,@(map (lambda (clause)
                            (syntax-case clause (->)
                              [(ps -> e)                    #`(corefn-case-clause (#,@u*) (ps -> (#,k e)))]
                              [(ps (t -> e) (t* -> e*) ...) #`(corefn-case-clause (#,@u*) (ps (t -> (#,k e)) (t* -> (#,k e*)) ...))]))
                          #'(clause+ ...)))))))]))

  (define-syntax (%data code) (syntax-error code "misplaced aux keyword"))

  (define-syntax %array
    (syntax-rules ()
      [(_ xs ...) (vector xs ...)]))

  (define-syntax (%object code)
    (syntax-case code ()
      [(m [k v] ...)
        (let ([k/v* (map
                      (lambda (k/v) (cons (datum->syntax #'m (string->symbol (syntax->datum (car k/v))))
                                          (cadr k/v)))
                      #'([k v] ...))])
          #`(let ([ht (make-hashtable symbol-hash symbol=? #,(length k/v*))])
              #,@(map (lambda (k/v) #`(symbol-hashtable-set! ht '#,(car k/v) #,(cdr k/v))) k/v*)
              ht))]))

  (define-syntax (%access code)
    (syntax-case code ()
      [(m ht x) #`(cdr (assert (symbol-hashtable-ref-cell ht '#,(datum->syntax #'m (string->symbol (datum x))))))]))

  (define-syntax (%update code)
    (syntax-case code ()
      [(_ ht [k v] ...)
        (let ([k/v* (map
                      (lambda (k/v) (cons (datum->syntax #'m (string->symbol (syntax->datum (car k/v))))
                                          (cadr k/v)))
                      #'([k v] ...))])
          #`(let ([new-ht (hashtable-copy ht #t)])
              #,@(map (lambda (k/v) #`(symbol-hashtable-set! new-ht '#,(car k/v) #,(cdr k/v))) k/v*)
              new-ht))])))
