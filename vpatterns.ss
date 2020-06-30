; EXAMPLE USE CASES
#;(define (factorial n)
  (match n
    (0 1)
    (n (* n (factorial (- n 1))))))
; as in (map + '(1 2 3) '(3 2 1)) returns '(4 4 4)
#;(define (mymap f . lists)
  (match lists
    (((x . rest) ...) (cons (apply f x) (apply mymap f rest)))
    ((() ...) '())))

;TODO unit test vectors
;TODO unit test records
;TODO unit test predicates

; TODO add quasipatterns
(module vpatterns

  (match match-iter record-ref record-length record->list)

  (import chicken scheme srfi-1 lolevel)
  (use srfi-1 lolevel)

  ; Returns value of n'th field of record, in order of definition of
  ; the fields in the record. So
  ; (define-record-type pare
  ;   (pare x y)
  ;   pare?
  ;   (y get-y)
  ;   (x get-x))
  ;  (record-ref (make-pare 0 1) 0) ===> 1
  ;  (record-ref (make-pare 0 1) 1) ===> 0
  ; (define-record-type pair
  ;   (pair a b)
  ;   is-pair?
  ;   (a get-a)
  ;   (b get-b))
  ;  (record-ref (make-pair 0 1) 0) ===> 0
  ;  (record-ref (make-pair 0 1) 1) ===> 1

  ; n currently must be permitted to an expression evaluated to an integer.
  ; possible some implementations implement record-ref in syntax, which would
  ; require a reimplementation of record->list
  (define (record-ref r n)
    (record-instance-slot r n))
  ; Tests against the name argument of the define-record-type, i.e. `pair` in (define-record-type pair ...)
  ; Chicken scheme doesn't bind a runtime object to the name: it compares against a symbol, so we have
  ; to quote the type argument with macros

  ;r and type will always be naked symbols: can implement as macro as seen below
  (define-syntax record-type?
    (syntax-rules ()
      ((_ r type) (record-instance? r 'type))))
  ; number of fields - 1, excluding type
  ; r will always be a naked symbol: can implement as macro
  (define (record-length r)
    (record-instance-length r))

  (define (record->list r)
    (let loop ((idx (- (record-length r) 1)) (acc '()))
      (if (< idx 0)
          acc
          (loop (- idx 1) (cons (record-ref r idx) acc)))))
(define-syntax match-ellipses
  (syntax-rules (quote)
    ((match-ellipses s 'pattern 'datum '(symbols ...) '(renamed ...) '(rest ...) '(data ...) 'body 'fail)
     (if (list? datum)
         (let loop ((ellipses-data (reverse datum)) (symbols '()) ...)
           (if (null? ellipses-data)
               (match-iter (rest ...) (data ...) body fail)
               (let ((renamed symbols) ...)
                 (match-iter (pattern) ((car ellipses-data))
                   (loop (cdr ellipses-data) (cons symbols renamed) ...)
                   fail))))
          fail)
     )))
(define-syntax match-iter
  (syntax-rules ::: (_ quote ... $ ?)
    ((match-iter () () body fail) body)
    ((match-iter (_ rest :::) (datum data :::) body fail)
     (match-iter (rest :::) (data :::) body fail))
    ((match-iter ('x rest :::) (datum data :::) body fail)
     (if (equal? 'x datum)
         (match-iter (rest :::) (data :::) body fail)
         fail))
    ((match-iter ((? pred x) rest :::) (datum data :::) body fail)
     (if (pred datum)
         (match-iter (x rest :::) (datum data :::) body fail)
         fail))
    ((match-iter (($ type field :::) rest :::) (datum data :::) body fail)
     (if (record-type? datum type)
         (let ((lst (record->list datum)))
          (match-iter ((field :::) rest :::) (lst data :::) body fail))
         fail))
    ((match-iter ((a ... b bs :::) rest :::) (datum data :::) body fail)
     (let ((coda-len (length '(b bs :::))))
      (if (list? datum)
          (let ((ellipses (drop-right datum coda-len))
                (coda (take-right datum coda-len)))
            (match-iter ((a ...) (b bs :::) rest :::) (ellipses coda data :::) body fail))
          fail)))
    ((match-iter ((a ...) rest :::) (datum data :::) body fail)
     (ck ()
       (match-ellipses
         'a
         'datum
         (deliteral (moulder 'a))
         (gensyms (deliteral (moulder 'a)))
         '(rest :::)
         '(data :::)
         'body
         'fail)))
    ((match-iter ((a ... . q) rest :::) (datum data :::) body fail)
     (syntax-error "match: ellipses lists must be proper" '(a ... . q)))
    ((match-iter ((a . b) rest :::) (datum data :::) body fail)
     (if (pair? datum)
         (let ((x (car datum)) (y (cdr datum)))
          (match-iter (a b rest :::) (x y data :::) body fail))
         fail))
    ((match-iter (#(a :::) rest :::) (datum data :::) body fail)
     (if (vector? datum)
         (let ((lst (vector->list datum)))
          (match-iter ((a :::) rest :::) (lst data :::) body fail))
         fail))
    ((match-iter (atom rest :::) (datum data :::) body fail)
     (letrec-syntax
          ; separated from test-rule as a workaround for chicken bug
          ((is-symbol
            (syntax-rules $$$ ()
              ((is_symbol) (let ((atom datum)) (match-iter (rest :::) (data :::) body fail)))))
           (test-rule
            (syntax-rules $$$ ()
              ((test-rule atom) (is-symbol))
              ; atom has to be quoted just in case it's ()
              ; all atoms at this point: numbers, chars, bools, except () are self evaluating
              ((test-rule . whatever)
               (if (equal? 'atom datum)
                   (match-iter (rest :::) (data :::) body fail)
                   fail)))))
        (test-rule (#f))))))
(define-syntax match
  (syntax-rules (else =>)
    ((match "##match-case-secret" data) (error "match: No patterns matched."))
    ((match "##match-case-secret" data (else body ...)) (begin body ...))
    ((match "##match-case-secret" data (else body ...) rest ...) (syntax-error "match: Clauses after else clause" 'rest ...))
    ((match "##match-case-secret" data (pattern => f) rest ...)
     (ck () (ck-list 'match '"##match-case-secret" 'data (ck-list 'pattern (ck-cons 'f (deliteral (moulder 'pattern)))) 'rest ...)))
    ((match "##match-case-secret" data (pattern body ...) rest ...)
     ; delay the next pattern to be made in a thunk
     (let ((next-pattern (lambda () (match "##match-case-secret" data rest ...))))
       ; we're going to either return a success thunk or a failure thunk. Evaluate it.
       ; We use the continuation k to bail out of a bad pattern and return the code for the next pattern thunk
       ((call/cc
         (lambda (k) 
           ; Wrap the body for the pattern in a thunk. Because this is a macro will have
           ; lexical scope regardless. The failure expression is to bail and evaluate the next pattern
           (match-iter (pattern) (data) (lambda () body ...) (k next-pattern)))))))
    ((match data rest ...)
     (let ((evaled data))
      (match "##match-case-secret" evaled rest ...)))))
(define-syntax ck
  (syntax-rules (quote)
    ((ck () 'v) v)
    ; Expression v is quoted. Evaluate remaining args `ea ...`
    ((ck (((op ...) ea ...) . s) 'v)
     (ck s "arg" (op ... 'v) ea ...))
    ; All arguments `va ...` are evaluated. Time to apply `op`
    ((ck s "arg" (op va ...))
     (op s va ...))
    ; Optimization with quoted value
    ((ck s "arg" (op ...) 'v eas ...)
     (ck s "arg" (op ... 'v) eas ...))
    ; Check argument ea
    ((ck s "arg" (op ...) ea eas ...)
     (ck (((op ...) eas ...) . s) ea))
    ; Expression is application. Evaluate arguments
    ((ck s (op ea ...))
     (ck s "arg" (op) ea ...))
  ))
(define-syntax ck-list
  (syntax-rules (quote)
    ((_ s 'x ...) (ck s '(x ...)))))
(define-syntax ck-cons
  (syntax-rules (quote)
    ((_ s 'x 'y) (ck s '(x . y)))))
(define-syntax ck-quote
  (syntax-rules ()
    ; x is already quoted. Double quote, 
    ((_ s x) (ck s 'x))))
(define-syntax moulder
  (syntax-rules (quote)
    ((moulder s 'tree) (moulder s "loop" () tree))
    ((moulder s "loop" vars (a . b) rest ...)
     (moulder s "loop" vars a b rest ...))
    ((moulder s "loop" vars #(a ...) rest ...)
     (moulder s "loop" vars a ... rest ...))
    ((moulder s "loop" (vars ...) a rest ...)
     (moulder s "loop" (vars ... a) rest ...))
    ((moulder s "loop" vars)
     (ck s 'vars))
  ))
(define-syntax gensyms
  (syntax-rules (quote)
    ((gensyms s 'syms) (gensyms s "loop" () syms))
    ((gensyms s "loop" new (a . rest))
     (gensyms s "loop" (x . new) rest))
    ((gensyms s "loop" new ())
     (ck s 'new))))
(define-syntax deliteral
  (syntax-rules ::: (quote ...)
    ((deliteral s '(vars :::)) (deliteral s "loop" () vars :::))
    ((deliteral s "loop" (vars :::) ... rest :::)
     (deliteral s "loop" (vars :::) rest :::))
    ((deliteral s "loop" (vars :::) atom rest :::)
     (letrec-syntax
      ; separated from test-rule as a workaround for chicken bug
      ; or possibly arcane macrology
      ((is-symbol
        (syntax-rules $$$ ()
          ((_) (deliteral s "loop" (vars ::: atom) rest :::))))
       (is-literal
        (syntax-rules $$$ ()
          ((_) (deliteral s "loop" (vars :::) rest :::))))
       (test-rule
        (syntax-rules $$$ ()
          ((test-rule atom) (is-symbol))
          ; atom has to be quoted just in case it's ()
          ((test-rule . _) (is-literal)))))
      (test-rule (#f))))
    ((deliteral s "loop" vars)
     (ck s 'vars))))
)
