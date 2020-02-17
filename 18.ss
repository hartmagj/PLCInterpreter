(load "D:\\CSSE 304\\Assignments\\chez-init.ss")
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
    (proc-names (list-of symbol?))
    (idss (list-of (list-of symbol?)))
    (bodiess (list-of (list-of expression?)))
    (letrec-bodies (list-of expression?))]
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
   (body expression?)]
  [app-exp
   (rator expression?)
   (rand (lambda (v) (or (expression? v) (list-of expression?))))]
  [named-let-exp
    (proc symbol?)
    (ids (list-of symbol?))
    (call-vals (list-of expression?))
    (bodies (list-of expression?))]
  [define-exp
    (sym expression?)
    (val expression?)])

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
  [root-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)]
  [recursive-env-reord
    (proc-names (list-of symbol?))
    (idss (list-of (list-of symbol?)))
    (bodiess (list-of (list-of expression?)))
    (old-env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [k-proc
    (k continuation?)]
  [exit-proc]
  [closure
  (syms (lambda (v) (or (list-of symbol? v) (null? v))))
  (body (lambda (v) (or (expression? v) (list-of expression?))))
  (env environment?)
  ]
   )

(define-datatype continuation continuation?
  [apply-k
    (proc procedure?)]
  [exit-k
    ]
  [if-k
    (iftrue expression?)
    (env environment?)
    (k continuation?)]
  [if-else-k
    (iftrue expression?)
    (iffalse expression?)
    (env environment?)
    (k continuation?)]
  [rator-k
    (rands (list-of expression?))
    (env list?)
    (k continuation?)]
  [rands-k
    (proc-val proc-val?)
    (k continuation?)]
  [set!-k
    (exp expression?)
    (env environment?)
    (k continuation?)]
  [or-k
    (body (list-of expression?))
    (env environment?)
    (k continuation?)]
  [and-k
    (body (list-of expression?))
    (env environment?)
    (k continuation?)]
  [bodies-k
    (bodies (list-of expression?))
    (env environment?)
    (k continuation?)]
  [global-k
    (id symbol?)
    (k continuation?)]
  [box-k
    (boxx box?)
    (k continuation?)]
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

; Again, you'll probably want to use your code from A11b
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
          [(eqv? (1st datum) 'define)
            (cond
              [(not (eq? (length datum) 3))
                (eopl:error 'parse-exp "Error in parse-exp: define-expression: incorrect length:" datum)]
              [(not (symbol? (2nd datum)))
                (eopl:error 'parse-exp "Error in parse-exp: define-expression: first arg must be a symbol:" datum)]
              [else
                (define-exp (parse-exp (2nd datum)) (apply parse-exp (cddr datum)))])]
          [(andmap (lambda (x) (ormap (lambda (pred) (pred x)) (list number? boolean? string? vector?))) datum) (lit-exp datum)]
          [(eqv? (1st datum) 'quote) (lit-exp (2nd datum))]
          
          [(and (eqv? (1st datum) 'let) (symbol? (2nd datum))) ;named-let case
            (cond
              [(not (> (length datum) 2)) (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length:" datum)]
              [(not (list? (3rd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: declaration in let is not a list:" datum)]
              [(not (andmap list? (3rd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: all let variables are not represented as proper lists: " datum)]
              [(not (andmap (lambda (x) (= 2 (length x))) (3rd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: declaration in let must be a list of length 2:" datum)]
              [(not (andmap symbol? (map 1st (3rd datum)))) (eopl:error 'parse-exp "Error in parse-exp: let expression: vars in let-exp must be symbols:" datum)]
              [else 
                (named-let-exp
                  (2nd datum)
                  (map 1st (3rd datum))
                  (map parse-exp (map 2nd (3rd datum)))
                  (map parse-exp (cdddr datum)))]
            )]
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
            [else (set!-exp (2nd datum) (parse-exp (3rd datum)))]
            )
          ]
          [(eqv? (1st datum) 'letrec)
          (cond
            [(not (> (length datum) 2)) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: incorrect length:" datum)]
            [(not (list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: invalid arguments:" datum)]
            [(not (andmap (lambda (x) (= 2 (length x))) (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: declaration in letrec must be a list of length 2:" datum)]
            [(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: expression is not a proper list:" datum)]
            [(not (andmap symbol? (map 1st (2nd datum)))) (eopl:error 'parse-exp "Error in parse-exp: letrec expression: vars in let-exp must be symbols:" datum)]
            [else
              (letrec-exp
                (map 1st (2nd datum))
                (map 2nd (map 2nd (2nd datum)))
                (map (lambda (x) (map parse-exp x)) (map cddr (map 2nd (2nd datum))))
                (map parse-exp (cddr datum)))]
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
        [define-exp (sym val)
          (cons 'define (cons (unparse-exp sym) (list (unparse-exp val))))]
        [let-exp (id body)
        (cons 'let (cons (map list (map unparse-exp (map 1st id)) (map unparse-exp (map 2nd id))) (map unparse-exp body)))
          ]
        [letrec-exp (proc-names idss bodiess letrec-bodies)
        ;(cons 'letrec (cons (map list (map unparse-exp (map 1st id)) (map unparse-exp (map 2nd id))) (map unparse-exp body)))
          (display "update unparse letrec")
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
            (list (unparse-exp rator) (unparse-exp rand)))]
        [else
          (display "unparse error")])))

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

(define root-env
  (lambda ()
    (root-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map box vals) env)))

(define make-closure
  (lambda (ids bodies env)
    (closure ids bodies env)
    ))

(define recursive-env
  (lambda (proc-names idss bodiess env)
    (recursive-env-reord proc-names idss bodiess env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
      [(eq? sym (car los)) pos]
      [else (loop (cdr los) (add1 pos))]))))
      
(define apply-env-help
  (lambda (env sym k) 
    (cases environment env 
      [root-env-record ()      
        (eopl:error 'env "variable ~s not found." sym)]
      [empty-env-record ()
        (apply-env-help init-env sym k)]
      [extended-env-record (syms vals env)
  (let ((pos (list-find-position sym syms)))
          (if (number? pos)
        (list-ref vals pos)
        (apply-env-help env sym k)))]
      [recursive-env-reord (proc-names idss bodiess old-env)
        (let ([pos (list-find-position sym proc-names)])
          (if (number? pos)
            (make-closure (list-ref idss pos)
              (list-ref bodiess pos)
              env)
            (apply-env-help old-env sym k)))]
        [else
          (display "apply-env-help error")])))

(define apply-env
  (lambda (env sym k)
    (let ([helpVal (apply-env-help env sym k)])
      (if (box? helpVal)
        (apply-continuation k (unbox helpVal))
        (apply-continuation k helpVal)))))

(define add-to-glob-env
  (lambda (s v)
    (cases environment init-env
      [extended-env-record (syms vals env)
        (if (list-contains? s syms)
          (let ([nSyms (remove s syms)]
                [nVals (remq (unbox (list-ref vals (list-find-position s syms))) (map unbox vals))])
            (set! init-env (extend-env (cons s nSyms) (cons v nVals) env)))
          (set! init-env (extend-env (cons s syms) (cons v (map unbox vals)) env)))]
      [else
        (display "error: global env is not an extended-env-record")])))


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
      [begin-exp (body)
        (app-exp [lambda-exp '() (map syntax-expand (2nd exp))] '())]
      ; [case-exp (conditional body)
      ; (syntax-expand (let-exp (list ())))
      ; ]
      [named-let-exp (proc ids call-vals bodies)
        (letrec-exp 
          (list proc)
          (list ids)
          (list (map syntax-expand bodies))
          (list (app-exp (var-exp proc) (map syntax-expand call-vals))))]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
        (letrec-exp
          proc-names
          idss
          (map (lambda (x) (map syntax-expand x)) bodiess)
          (map syntax-expand letrec-bodies))]
      [else exp]
      )))


;(define let*-exp
(define let*-help
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
    (eval-exp form (empty-env) (exit-k))))

; eval-exp is the main component of the interpreter
(define eval-let
  (lambda (bodies env k)
    (if (null? (cdr bodies))
      (eval-exp (syntax-expand (1st bodies)) env k)
      (eval-exp (syntax-expand (1st bodies)) env (bodies-k (cdr bodies) env k))
      )))


(define eval-exp
  (lambda (express env k)
    (let ([exp (syntax-expand express)])
      (cases expression exp
        [lit-exp (datum)(apply-continuation k datum)]
        [var-exp (id)
          (apply-env env id k)]
         ; [app-exp (rator rands)
         ;  (let ([proc-value (eval-exp rator env)]
         ;        [args (check-quote rator rands env)])
         ;    (apply-proc proc-value args))]
         [app-exp (rator rands)
          (eval-exp rator env (rator-k rands env k))
          ]
        [lambda-exp (id body)
          (cond
            [(null? id)
              (apply-continuation k (make-closure id body env))]
            [(and (list? (car id)) (list-contains? "." id))
              (apply-continuation k (make-closure (make-imp (map-lr unparse-exp (remove "." id))) body env))]
            [(list? (car id))
              (apply-continuation k (make-closure (map-lr unparse-exp id) body env))]
            [else
              (apply-continuation k (make-closure (unparse-exp id) body env))])
        ]
        [if-exp (test iftrue)
        (if (equal? test '(var-exp else)) (eval-exp (syntax-expand iftrue) env k)
          (eval-exp test env (if-k iftrue env k))
          )
        ]
        [if-else-exp (test iftrue iffalse)
          (eval-exp test env (if-else-k iftrue iffalse env k))]
        [begin-exp (body)
          (eval-exp (syntax-expand exp) env k)]
        [or-exp (body)
        (if (null? body)
          (apply-continuation k #f)
          (eval-exp (car body) env (or-k (cdr body) env k))
        )
        ]
        [and-exp (body)
        (if (null? body)
          (apply-continuation k #t)
          (eval-exp (car body) (env (and-k (cdr body) env k)))
        )
        ]
        [let-exp (id body)
           ;(eval-let body (extend-env (map 2nd (map 1st id)) (map (lambda (x) (eval-exp x env)) (map 2nd id)) env))]
           (eval-exp (syntax-expand exp) env k)
        ]
        [while-exp (test body)
        (letrec ([loop (lambda () (if (eval-exp test env k) 
          (begin (eval-exp (syntax-expand body) env k) (loop))
          ))]) (loop))
        ]
        [set!-exp (var body)
          (apply-continuation (set!-k body env k) (apply-env-help env var (set!-k body env k)))
            ]
        [letrec-exp (proc-names idss bodiess letrec-bodies)
          (eval-let letrec-bodies (recursive-env proc-names idss (map list (map syntax-expand (map car bodiess))) env) k)]
        [define-exp (sym val)
          (eval-exp (syntax-expand val) env (global-k (unparse-exp sym) k))]
        
        [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))

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
; (define (apply-env-ref-global sym env)

;   )
; finds if a given object is in a list
(define list-contains?
  (lambda (n li)
    (if (null? li)
      #f
      (if (equal? n (car li))
        #t
        (list-contains? n (cdr li))))))

; checks the rator for a quote operator, if so it opts out of evaluating the rands
; (define check-quote
;   (lambda (rator rands env)
;     (if (equal? (cadr rator) 'quote)
;           (map unparse-exp rands)
;           (eval-rands rands env k))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env k)
    (map-cps-2 (lambda (x k2) (eval-exp (syntax-expand x) env k2)) rands k)))

(define map-cps-2
  (lambda (proc ls k)
    (if (null? ls)
      (apply-continuation k '())
      (map-cps-2 proc (cdr ls)
        (apply-k (lambda (rls)
                          (proc (car ls)
                            (apply-k (lambda (result)
                                              (apply-continuation k (cons result rls)))))))))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args k)]
      [k-proc (kp) (apply-continuation kp (1st args))]
      [exit-proc () (apply-continuation (exit-k) args)]
      [closure (id bodies env)
        ;(display id)
        (cond
          [(list? id)
            (eval-let bodies (extend-env id args env) k)]
          [(pair? id)
            (let ([res (match-imp-args id args)])
              (eval-let bodies (extend-env (car res) (cadr res) env) k))]
          [else
            (eval-let bodies (extend-env (list id) (list args) env) k)])
      ]
      
      ; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* 
  '(+ - * / add1 sub1 cons = >= <= < > quote list eq? equal? length list->vector 
    not zero? car cdr null? list? pair? vector->list vector? set-car! set-cdr!
    number? symbol? caar cadr cadar call/cc procedure? vector-ref vector apply map quotient member vector-set!
    eqv? append list-tail assq))

(define create-init-env
  (lambda ()
    (extend-env
      *prim-proc-names*
      (map prim-proc *prim-proc-names*)
      (root-env))))

(define init-env         ; for now, our initial global environment only contains 
  (create-init-env))

(define reset-global-env
  (lambda ()
    (set! init-env (create-init-env))))

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
  (lambda (prim-proc args k)
    (case prim-proc
      [(+) (apply-continuation k (apply + args))]
      [(-) (apply-continuation k (apply - args))]
      [(*) (apply-continuation k (apply * args))]
      [(/) (apply-continuation k (apply / args))]
      [(add1) (apply-continuation k (+ (1st args) 1))]
      [(sub1) (apply-continuation k (- (1st args) 1))]
      [(quotient) (apply-continuation k (apply quotient args))]
      [(member) (apply-continuation k (member (1st args) (2nd args)))]
      [(cons) (apply-continuation k (cons (1st args) (2nd args)))]
      [(=) (apply-continuation k (apply = args))]
      [(>=) (apply-continuation k (apply >= args))]
      [(<=) (apply-continuation k (apply <= args))]
      [(>) (apply-continuation k (apply > args))]
      [(<) (apply-continuation k (apply < args))]
      [(quote) (apply-continuation k (car args))]
      [(list) (apply-continuation k (apply list args))]
      [(eq?) (apply-continuation k (eq? (1st args) (2nd args)))]
      [(equal?) (apply-continuation k (equal? (1st args) (2nd args)))]
      [(length) (apply-continuation k (length(car  args)))]
      [(list->vector) (apply-continuation k (list->vector (car args)))]
      [(not) (apply-continuation k (not (car args)))]
      [(zero?) (apply-continuation k (zero? (car args)))]
      [(set-car!) (apply-continuation k (set-car! (1st args) (2nd args)))]
      [(set-cdr!) (apply-continuation k (set-cdr! (1st args) (2nd args)))]
      [(car) (apply-continuation k (car (1st args)))]
      [(cdr) (apply-continuation k (cdar args))] 
      [(null?) (apply-continuation k (null? (car args)))]
      [(list?) (apply-continuation k (list? (car args)))]
      [(pair?) (apply-continuation k (pair? (car args)))] 
      [(vector->list) (apply-continuation k (vector->list (1st args)))]
      [(vector?) (apply-continuation k (vector? (car args)))]
      [(number?) (apply-continuation k (number? (car args)))]
      [(symbol?) (apply-continuation k (symbol? (car args)))] 
      [(caar) (apply-continuation k (caar (car args)))]
      [(cadr) (apply-continuation k (cadr (car args)))]
      [(cadar) (apply-continuation k (cadar (car args)))]
      [(procedure?) (apply-continuation k (apply proc-val? args))]
      [(vector-ref) (apply-continuation k (vector-ref (1st args) (2nd args)))]
      [(vector-set!) (apply-continuation k (vector-set! (1st args) (2nd args) (3rd args)))]
      [(vector) (apply-continuation k (apply vector args))]
      [(apply) (apply-continuation k (apply apply-proc (append args (list (exit-k)))))]
      [(map) (map-cps (1st args) (map list (2nd args)) k)]
      [(eqv?) (apply-continuation k (eqv? (1st args) (2nd args)))]
      [(call/cc) (apply-proc (1st args) (list (k-proc k)) k)]
      [(append) (apply-continuation k (apply append args))]
      [(list-tail) (apply-continuation k (list-tail (1st args) (2nd args)))]
      [(assq) (apply-continuation k (assq (1st args) (2nd args)))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))
(define map-cps
  (lambda (proc ls k)
    (if (null? ls)
      (apply-continuation k '())
      (map-cps proc (cdr ls)
        (apply-k (lambda (rls)
                        (apply-proc proc (car ls)
                          (apply-k (lambda (result)
                            (apply-continuation k (cons result rls))))))))
        )))

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

(define apply-continuation
  (lambda (k val)
    (cases continuation k
      [apply-k (proc)
        (proc val)]
      [exit-k () val]
      [if-k (iftrue env k)
        (if val (eval-exp iftrue env k) (apply-continuation k (void)))]
      [if-else-k (iftrue iffalse env k)
        (if val (eval-exp iftrue env k) (eval-exp iffalse env k))]
      [rator-k (rands env k)
        (eval-rands rands env (rands-k val k))]
      [rands-k (proc k)
        (apply-proc proc val k)]
      [set!-k (exp env k)
        (eval-exp exp env (box-k val k))]
      [box-k (boxx k)
        (apply-continuation k (set-box! boxx val))]
      [or-k (body env k)
        (if val
          (apply-continuation k val)
          (if (null? body)
            (apply-continuation k #f)
            (eval-exp (1st body) env (or-k (cdr body) env k))))]
      [and-k (body env k)
        (if val
          (if (null? body)
            (apply-continuation k #t)
            (eval-exp (1st body) env (and-k (cdr body) env k))))]
      [bodies-k (body env k)
        (eval-let body env k)]
      [global-k (id k)
        (apply-continuation k (add-to-glob-env id val))]
      [else val]
        )))