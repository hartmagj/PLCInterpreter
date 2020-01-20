;:  By: Reyd Nguyen and Grant Hartman

;(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
   [lit-exp
   (id lit?)]
   [lambda-exp
   (id (lambda (v) (or (expression? v) (list-of expression?))))
   (body (lambda (v) (or (expression? v) (list-of expression?))))]
   [let-exp
   (id (list-of (list-of expression?)))
   (body (list-of expression?))]
   [letrec-exp
   (id (list-of (list-of expression?)))
   (body (list-of expression?))]
   [if-exp
   (boolean expression?)
   (iftrue expression?)]
   [if-else-exp
   (boolean expression?)
   (iftrue expression?)
   (iffalse expression?)]
   [let*-exp
   (id (list-of (list-of expression?)))
   (body (list-of expression?))]
   [set!-exp
   (id symbol?)
   (body (list-of expression?))]
   [app-exp
   (rator expression?)
   (rand (lambda (v) (or (expression? v) (list-of expression?))))])

; helper procedure
(define lit?
  (lambda (v)
    (cond
      [(number? v) #t]
      [(string? v) #t]
      [(boolean? v) #t]
      [(vector? v) #t]
      [(char? v) #t]
      [(null? v) #t]
      [else #f]
      )))
  

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)])

(define-datatype closure closure?
  [full-closure
  (syms (list-of symbol?))
  (body (list-of expression?))
  (env environment?)
  ]
  )


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])

  
;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

; Again, you'll probably want to use your code form A11b

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
        [(number? datum) (lit-exp datum)]
        [(string? datum) (lit-exp datum)]
        [(boolean? datum) (lit-exp datum)]
        [(char? datum) (lit-exp datum)]
        [(vector? datum) (lit-exp datum)]
        [(null? datum) (lit-exp datum)]
        [(not (list? datum))
          (eopl:error 'parse-exp "Error in parse-exp: attempt to apply non-list: " datum)]
        [(pair? datum)
        (cond
          [(eqv? (1st datum) 'lambda)
            (cond
              [(<(length datum) 3) 
                (eopl:error 'parse-exp "Error in parse-exp: lambda-expression: incorrect length:" datum)]
              [(not (valid-lambda-var? (2nd datum)))
                (eopl:error 'parse-exp "Error in parse-exp: lambda-expression: lambda var declaration must contain all symbols:" datum)]
              [else
                (lambda-exp (imp-list-apply parse-exp (2nd datum)) (imp-list-apply parse-exp (cddr datum)))]
            )
          ]
          [(eqv? (1st datum) 'let)
          (cond
            [(not (> (length datum) 2)) (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length:" datum)]
            [(not (list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: declaration in let is not a list:" datum)]
            [(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: all let variables are not represented as proper lists: " datum)]
            [(not (andmap (lambda (x) (= 2 (length x))) (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: declaration in let must be a list of length 2:" datum)]
            [(not (andmap symbol? (map 1st (2nd datum)))) (eopl:error 'parse-exp "Error in parse-exp: let expression: vars in let-exp must be symbols:" datum)]
            [else (let-exp (map list (imp-list-apply parse-exp (map 1st (2nd datum))) (imp-list-apply parse-exp (map 2nd (2nd datum)))) (map parse-exp (cddr datum)))]
            )
          ]
          [(eqv? (1st datum) 'if)
          (cond
            [(or (< (length datum) 3) (> (length datum) 4)) (eopl:error 'parse-exp "Error in parse-exp: if expression: incorrect length :" datum)]
            [(= (length datum) 3) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
            [else (if-else-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (cadddr datum)))]
            )
          ]
          [(eqv? (1st datum) 'set!)
          (cond 
            [(not (= (length datum) 3)) (eopl:error 'parse-exp "Error in parse-exp: set! expression: incorrect length:" datum)]
            [else (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
            )
          ]
          [(eqv? (1st datum) 'letrec)
          (cond
            [(not (> (length datum) 2)) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: incorrect length:" datum)]
            [(not (list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: invalid arguments:" datum)]
            [(not (andmap (lambda (x) (= 2 (length x))) (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: declaration in letrec must be a list of length 2:" datum)]
            [(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: expression is not a proper list:" datum)]
            [(not (andmap symbol? (map 1st (2nd datum)))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: vars in let-exp must be symbols:" datum)]
            [else (letrec-exp (map list (imp-list-apply parse-exp (map 1st (2nd datum))) (imp-list-apply parse-exp (map 2nd (2nd datum)))) (imp-list-apply parse-exp (cddr datum)))]
            )
          ]
          [(eqv? (1st datum) 'let*)
          (cond
            [(not (> (length datum) 2)) (eopl:error 'parse-exp "Error in parse-exp: let** expression: incorrect length: " datum)]
            [(not (list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let* expression: declaration in let* is not a list:" datum)]
            [(not (andmap (lambda (x) (= 2 (length x))) (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let* expression: declaration in let* must be a list of length 2")]
            [(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let* expression: expression is not a proper list")]
            [(not (andmap symbol? (map 1st (2nd datum)))) (eopl:error 'parse-exp "Error in parse-exp: let* expression: vars in let*-exp must be symbols")]
            [else (let*-exp (map list (imp-list-apply parse-exp (map 1st (2nd datum))) (imp-list-apply parse-exp (map 2nd (2nd datum)))) (imp-list-apply parse-exp (cddr datum)))]
            )
          ]
          [else (app-exp (parse-exp (1st datum))
            (imp-list-apply parse-exp (cdr datum)))])]
        [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))


(define unparse-exp
  (lambda (datum)
    (cases expression datum
        [var-exp (id)
          id]
        [lit-exp (id)
          id]
        [lambda-exp (id body)
        (cond
          [(null? id) (cons 'lambda (cons '() (map unparse-exp body)))]
          [(list? (1st id)) (cons 'lambda (cons (map unparse-exp id) (map unparse-exp body)))]
          [else (cons 'lambda (cons (unparse-exp id) (map unparse-exp body)))]
          )
          ]
        [let-exp (id body)
        (cons 'let (cons (map list (map unparse-exp (map 1st id)) (map unparse-exp (map 2nd id))) (map unparse-exp body)))
          ]
        [letrec-exp (id body)
        (cons 'letrec (cons (map list (map unparse-exp (map 1st id)) (map unparse-exp (map 2nd id))) (map unparse-exp body)))

          ]
        [let*-exp (id body)
        (cons 'let* (cons (map list (map unparse-exp (map 1st id)) (map unparse-exp (map 2nd id))) (map unparse-exp body)))
          ]
        [if-exp (bool iftrue)
        (list 'if (unparse-exp bool) (unparse-exp iftrue))
          ]
        [if-else-exp (bool iftrue iffalse)
        (list 'if (unparse-exp bool) (unparse-exp iftrue) (unparse-exp iffalse))
          ]
        [set!-exp (id body)
        (list 'set! (unparse-exp id) (unparse-exp body))
          ]
        [app-exp (rator rand)
          (if (list? rand)
            (cons (unparse-exp rator) (map unparse-exp rand))
            (list (unparse-exp rator) (unparse-exp rand)))])))

; helpful functions for parser
(define var-exp?
 (lambda (x)
   (cases expression x
     [var-exp (id) #t]
     [else #f])))

(define valid-lambda-var?
  (lambda (datum)
    (cond
      [(symbol? datum)
        #t]
      [(null? datum)
        #t]
      [(pair? datum)
        (and (valid-lambda-var? (car datum)) (valid-lambda-var? (cdr datum)))]
      [else
        #f])))

(define imp-list-apply
  (lambda (proc iList)
    (cond
      [(null? iList)
        '()]
      [(list? iList)
        (map proc iList)]
      [(not (pair? iList))
        (proc iList)]
      [(not (pair? (cdr iList)))
        (cons (proc (car iList)) (append '(".") (list (proc (cdr iList)))))]
      [else
        (cons (proc (car iList)) (imp-list-apply proc (cdr iList)))])))

(define imp-list-unparse
  (lambda (iList)
    (cond
      [(null? iList)
        '()]
      [(null? (cdr iList))
        (list (unparse-exp (1st iList)))]
      [(equal? "." (2nd iList))
        (cons (cons (unparse-exp (1st iList)) (unparse-exp (3rd iList))) (imp-list-unparse (cddd r iList)))]
      [else
        (cons (unparse-exp (1st iList)) (imp-list-unparse (cdr iList)))])))

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
      [(eq? sym (car los)) pos]
      [else (loop (cdr los) (add1 pos))]))))
      
(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
        (eopl:error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
  (let ((pos (list-find-position sym syms)))
          (if (number? pos)
        (list-ref vals pos)
        (apply-env env sym)))])))


;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

; To be added in assignment 14.

;--------------------------------------+
;                                      |
;   CONTINUATION DATATYPE and APPLY-K  |
;                                      |
;--------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+


; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
  (apply-env env id)]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (check-quote rator rands)])
          (apply-proc proc-value args))]
      [if-else-exp (test iftrue iffalse)
        (if (eval-exp test env)
          (eval-exp iftrue env)
          (eval-exp iffalse env))]
      
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; (define eval-bodies
;   (lambda (body env)
;     ()))
; checks the rator for a quote operator, if so it opts out of evaluating the rands
(define check-quote
  (lambda (rator rands)
    (if (equal? (cadr rator) 'quote)
          (map unparse-exp rands)
          (eval-rands rands))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands)
    (map eval-exp rands env)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (id bodies env)
      (eval-bodies bodies (extend-env id args env))
      ]
      ; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* 
  '(+ - * / add1 sub1 cons = >= <= quote list eq? equal? length list->vector 
    not zero? car cdr null? list? pair? vector->list vector? 
    number? symbol? caar cadr cadar procedure?))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (display args)]
      [(=) (apply = args)]
      [(>=) (apply >= args)]
      [(<=) (apply <= args)]
      [(quote) (car args)]
      [(list) (apply list args)]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(length) (length(car  args))]
      [(list->vector) (list->vector args)]
      [(not) (not (car args))]
      [(zero?) (zero? (car args))]
      [(car) (1st args)]
      [(cdr) (cdr args)]
      [(procedure?)]
      [(null?) (null? (car args))]
      [(list?) (list? (car args))]
      [(pair?) (pair? (car args))]
      [(vector->list) (vector->list (car args))]
      [(vector?) (vector? (car args))]
      [(number?) (number? (car args))]
      [(symbol?) (symbol? (car args))]
      [(caar) (caaar args)]
      [(cadr) (cadar args)]
      [(cadar) (cadaar args)]
      [(procedure?) (procedure? (car args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))