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
   [begin-exp
    (body (list-of expression?))]
   [cond-exp
    (body (list-of (list-of expression?)))]
   [and-exp
     (body (list-of expression?))]
   [or-exp
     (body (list-of expression?))]
   [case-exp
     (condi expression?)
     (body (list-of (lambda (x) (expression? (2nd x)) )))] 
   [while-exp
     (condi expression?)
     (body expression?)]
   [let*-exp
      (vari (list-of (list-of expression?)))
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
    (ormap (lambda (pred) (pred v))(list number? vector? boolean? symbol? string? pair? null?))
    ))
  

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
  (syms (lambda (v) (or (list-of symbol? v) (null? v))))
  (body (lambda (v) (or (expression? v) (list-of expression?))))
  (env environment?)
  ]
   )

  
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
          [(andmap (lambda (x) (ormap (lambda (pred) (pred x)) (list number? boolean? string? vector?))) datum) (lit-exp datum)]
          [(eqv? (1st datum) 'quote) (lit-exp (2nd datum))]
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
          [(eqv? (1st datum) 'begin)
            (begin-exp (map parse-exp (cdr datum)))]
       [(eqv? (1st datum) 'cond)
        (cond-exp (map (lambda (x) (list (parse-exp (1st x)) (parse-exp (2nd x)))) (cdr datum)))]
       [(eqv? (1st datum) 'and)
        (and-exp (map parse-exp (cdr datum)))]
       [(eqv? (1st datum) 'or)
        (or-exp (map parse-exp (cdr datum)))]
       [(eqv? (1st datum) 'case)
        (case-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
       [(eqv? (1st datum) 'while)
        (while-exp (parse-exp (2nd datum)) (begin-exp (map parse-exp (cddr datum))))] 
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
        [begin-exp (body)
        (cons 'begin (map unparse-exp body))
        ]
        [cond-exp (body)
        (list 'cond (map unparse-exp body))
        ]
        [and-exp (body) (cons 'and (map unparse-exp body))]
        [or-exp (body) (cons 'or (map unparse-exp body))]
        [case-exp (condi body) 
        (list 'case (unparse-exp condi) (map unparse-exp body))
        ]
        [while-exp (condi body)
        (list 'while (unparse-exp condi) (unparse-exp body))
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

(define make-closure
  (lambda (ids bodies env)
    (closure ids bodies env)
    ))

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

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [let-exp (id body)
      (app-exp (lambda-exp (map 1st id) (map syntax-expand body)) (map 2nd id))]
      [let*-exp (id body)
      (syntax-expand (let*-help id body))]
      [cond-exp (body)
      (cond-helper body)]
      [case-exp (condition body)
      (syntax-expand (let-exp (list (list (var-exp 'x) condition)) (list (case-help condition body))))
      ]
      ; [case-exp (conditional body)
      ; (syntax-expand (let-exp (list ())))
      ; ]
      [else exp]
      )))

(define let*-exp
  (lambda (id body)
    (if(null? id)
      (let-exp '() body)
      (let-exp (list(car id)) (list (syntax-expand (let*-exp (cdr id) body))))
      ))
  )
(define cond-helper
  (lambda (body)
    (if (= (length body) 1)
      (if-exp (caar body) (cadar body))
      (if-else-exp (caar body) (cadar body) (cond-helper (cdr body)))
      )))
(define case-help
  (lambda (condition body)
    (if (= (length body) 1)
      (1st (caddar body))
      (if-else-exp (app-exp (var-exp 'member) (list (var-exp 'x) (cadar body))) 
        (1st (caddar body)) (case-help condition (cdr body)))
      )))
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
(define eval-let
  (lambda (bodies env)
    (if (null? (cdr bodies))
      (eval-exp (car bodies) env)
      (begin
        (eval-exp (1st bodies) env)
        (eval-let (cdr bodies) env)))))


(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
        (apply-env env id)]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (check-quote rator rands env)])
          (apply-proc proc-value args))]
      [lambda-exp (id body)
        (cond
          [(null? id)
            (make-closure id body env)]
          [(and (list? (car id)) (list-contains? "." id))
            (make-closure (make-imp (map-lr unparse-exp (remove "." id))) body env)]
          [(list? (car id))
            (make-closure (map-lr unparse-exp id) body env)]
          [else
            (make-closure (unparse-exp id) body env)])
      ]
      [if-exp (test iftrue)
      (if (equal? test '(var-exp else)) (eval-exp iftrue env)
        (if (eval-exp test env) (eval-exp iftrue env))
        )
      ]
      [if-else-exp (test iftrue iffalse)
        (if (eval-exp test env)
          (eval-exp iftrue env)
          (eval-exp iffalse env))]
      [begin-exp (body)
      (for-each (lambda (x) (eval-exp x env)) (map syntax-expand body))]
      [or-exp (body)
      (if (null? body)
      #f
      (let ([temp (eval-exp (syntax-expand (1st body)) env)])
        (if temp
          temp
          (eval-exp (or-exp (cdr body)) env)
          )
        ))
      ]
      [and-exp (body)
      (if (null? body)
      #t
      (let ([temp (eval-exp (syntax-expand (1st body)) env)])
        (if temp
          (eval-exp (syntax-expand (car body)) env)
          #f
          )
        ))
      ]
      [let-exp (id body)
         ;(eval-let body (extend-env (map 2nd (map 1st id)) (map (lambda (x) (eval-exp x env)) (map 2nd id)) env))]
         (eval-exp (syntax-expand exp) env)
      ]
      [while-exp (test body)
      (letrec ([loop (lambda () (if (eval-exp test env) 
        (begin (eval-exp (syntax-expand body) env) (loop))
        ))]) (loop))
      ]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; maps from left to right
(define map-lr
  (lambda (proc li)
    (if (null? li)
      '()
      (cons (proc (car li)) (map-lr proc (cdr li))))))

(define make-imp
  (lambda (li)
    (if (eq? 1 (length (cdr li)))
      (cons (car li) (cadr li))
      (cons (car li) (make-imp (cdr li))))))

; finds if a given object is in a list
(define list-contains?
  (lambda (n li)
    (if (null? li)
      #f
      (if (equal? n (car li))
        #t
        (list-contains? n (cdr li))))))
; (define eval-bodies
;   (lambda (body env)
;     ()))
; checks the rator for a quote operator, if so it opts out of evaluating the rands
(define check-quote
  (lambda (rator rands env)
    (if (equal? (cadr rator) 'quote)
          (map unparse-exp rands)
          (eval-rands rands env))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (id bodies env)
        ;(display id)
        (cond
          [(list? id)
            (eval-let bodies (extend-env id args env))]
          [(pair? id)
            (let ([res (match-imp-args id args)])
              (eval-let bodies (extend-env (car res) (cadr res) env)))]
          [else
            (eval-let bodies (extend-env (list id) (list args) env))])
      ]
      ; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* 
  '(+ - * / add1 sub1 cons = >= <= < > quote list eq? equal? length list->vector 
    not zero? car cdr null? list? pair? vector->list vector? set-car! set-cdr!
    number? symbol? caar cadr cadar procedure? vector-ref vector apply map quotient member vector-set!))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; handles improper lists in closure id fields
(define match-imp-args
  (lambda (id args)
    (if (null? id)
      '(()())
      (if (not (pair? id))
        (let ([res (match-imp-args '() (cdr args))])
          (list (cons id (car res)) (cons args (cadr res))))
        (let ([res (match-imp-args (cdr id) (cdr args))])
          (list (cons (car id) (car res)) (cons (car args) (cadr res))))))))

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
      [(quotient) (apply quotient args)]
      [(member) (member (1st args) (2nd args))]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (apply = args)]
      [(>=) (apply >= args)]
      [(<=) (apply <= args)]
      [(>) (apply > args)]
      [(<) (apply < args)]
      [(quote) (car args)]
      [(list) (apply list args)]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(length) (length(car  args))]
      [(list->vector) (list->vector (car args))]
      [(not) (not (car args))]
      [(zero?) (zero? (car args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(cdr) (cdar args)]
      [(null?) (null? (car args))]
      [(list?) (list? (car args))]
      [(pair?) (pair? (car args))]
      [(vector->list) (vector->list (1st args))]
      [(vector?) (vector? (car args))]
      [(number?) (number? (car args))]
      [(symbol?) (symbol? (car args))]
      [(caar) (caar (car args))]
      [(cadr) (cadr (car args))]
      [(cadar) (cadar (car args))]
      [(procedure?) (apply proc-val? args)] 
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(vector) (apply vector args)]
      [(apply) (apply (lambda v (apply-proc (1st args) v)) (2nd args))]
      [(map) (map (lambda (v) (apply-proc (1st args) (list v))) (2nd args))]
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
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))