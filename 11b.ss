
(define-datatype expression expression?
  [var-exp
   (id symbol?)]
   [lit-exp
   (id lit?)]
   [lambda-exp
   (id (lambda (v) (or (symbol? v) (list-of expression?))))
   (body (list-of expression?))]

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
   (rand (list-of expression?))])

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
        [(null? datum) (lit-exp datum)]
        [(pair? datum)
        (cond
          [(eqv? (1st datum) 'lambda)
          (cond
            [(<(length datum) 2) (eopl:error 'parse-exp "Error in parse-exp: lambda-expression: incorrect length:" datum)]
            [(not (andmap symbol? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: lambda-expression: lambda must contain all symbols" datum)]
            [(symbol? (2nd datum)) (lambda-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
            [else (lambda-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
            )
          ]
          [(eqv? (1st datum) 'let)
          (cond
            [(< (length datum) 2) (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length")]
            [(not (list? (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: declaration in let is not a list")]
            [(not (andmap (lambda (x) (= 2 (length x))) (2nd datum))) (eopl:error 'parse-exp "Error in parse-exp: let expression: declaration in let must be a list of length 2")]
            [(not (andmap (list? (2nd datum)))) (eopl:error 'parse-exp "Error in parse-exp: let expression: expression is not a proper list")]
            [(not (andmap symbol? (map 1st (2nd datum)))) (eopl:error 'parse-exp "Error in parse-exp: let expression: vars in let-exp must be symbols")]
            [(else (let-exp (map list (map parse-exp (map 1st (2nd datum))) (map parse-exp (map 2nd (2nd datum)))) (map parse-exp (cddr exp))))]
            )
          ]
          




          [else (app-exp (parse-exp (1st datum))
            (map parse-exp (2nd datum)))])]
        [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))
; An auxiliary procedure that could be helpful.
(define var-exp?
 (lambda (x)
   (cases expression x
     [var-exp (id) #t]
     [else #f])))
(var-exp? (var-exp 'a))
(var-exp? (app-exp (var-exp 'a) (var-exp 'b))) 