(load "chez-init.ss")
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

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
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
              ; [(symbol? (2nd datum)) 
              ;   (lambda-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
              ; [else 
              ;   (lambda-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
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
; unparser on app-exp isn't working, it has to do with the fact that rand is a list of expressions i think

; An auxiliary procedure that could be helpful.
(define var-exp?
 (lambda (x)
   (cases expression x
     [var-exp (id) #t]
     [else #f])))
; (var-exp? (var-exp 'a))
; (var-exp? (app-exp (var-exp 'a) (var-exp 'b))) 

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