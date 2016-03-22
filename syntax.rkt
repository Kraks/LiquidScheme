#lang racket

(require rackunit)

#|
Language Syntax

<top> ::= <def>* <exp>*

<def> ::= (define <var> : <type> <exp>)
        | (define (<name> [<var> : <type>]) : <type> <exp>)

<exp> ::= <var>
        | <literal>
        | <prim>
        | (λ <label> [<var> : <type>] : <type> <exp>)
        | (if <exp> <exp> <exp>)
        | (let ((<var> : <type> <exp>)) <body>)
        | (<exp> <exp>)

<literal> ::= <int> | <bool>
<prim> ::= + | - | * | / | >= | <= | > | < | = | !=
         | and | or | not

<label> ::= <symbol>

=============

<type> ::= Int | Bool | Any
         | (-> <type> <type>)
         | (Int <predicate>) | (Bool <predicate>) | (Any #t)

<predicate> ::= #t | (<pred-op> <operand> <operand>)

<pred-op> ::= > | < | = | >= | <= | !=
            | and | or | not
<operand> ::= <predicate> | <literal> | _

|#

#|
Core Syntax

<top> ::= <def>* <exp>*

<def> ::= (define (<name> [<var> : <type>]) : <type> <exp>)

<exp> ::= <var>
        | <literal>
        | <prim>
        | (λ <label> [<var> : <type>] : <type> <exp>)
        | (if <exp> <exp> <exp>)
        | (<exp> <exp>)

<literal> ::= <int> | <bool>

<prim> ::= + | - | * | / | >= | > | =
         | and | or | not

<label> ::= <symbol>

=============

<type> ::= (-> <type> <type>)
         | (Int <predicate>) | (Bool <predicate>) | (Any #t)

<predicate> ::= #t | (<pred-op> <operand> <operand>)

<pred-op> ::= >= | > | =
            | and | or | not

<operand> ::= <predicate> | <literal> | _

|#

; TODO redundant type info in definition
; TODO adding Any type?
; TODO type of let body?
; TODO do we really need (quote ...)?
; TODO reduce pred-op, recursively?
; TODO do we really need all arith operators?
; TODO boolean predicate

(define (desugar expr)
  (match expr
    ; Define a lambda
    [`(define (,name [,var : ,atype]) : ,rtype ,exp)
     `(define ,name : (,(desugar-type atype) -> ,(desugar-type rtype))
        (lambda ,name [,var : ,(desugar-type atype)] : ,(desugar-type rtype) ,(desugar exp)))]
    ; Define a variable
    [`(define ,name : ,type ,exp)
     `(define ,name : ,(desugar-type type) ,(desugar exp))]
    ; If expression
    [`(if ,cnd ,thn ,els)
     `(if ,(desugar cnd) ,(desugar thn) ,(desugar els))]
    ; Lambda
    [`(lambda ,label [,var : ,atype] : ,rtype ,body)
     `(lambda ,label [,var : ,(desugar-type atype)] : ,(desugar-type rtype) ,(desugar body))]
    ; Let expression
    [`(let ((,var : ,type ,exp)) ,body)
     `((lambda ,(gensym 'let) [,var : ,(desugar-type type)] : (Any #t)
         ,(desugar body))
       ,(desugar exp))]
    ; Arithmetic operators
    [`(+ ,e1 ,e2)
     `(+ ,(desugar e1) ,(desugar e2))]
    [`(- ,e1 ,e2)
     `(- ,(desugar e1) ,(desugar e2))]
    [`(* ,e1 ,e2)
     `(* ,(desugar e1) ,(desugar e2))]
    [`(/ ,e1 ,e2)
     `(/ ,(desugar e1) ,(desugar e2))]
    [`(> ,e1 ,e2)
     `(> ,(desugar e1) ,(desugar e2))]
    [`(>= ,e1 ,e2)
     `(>= ,(desugar e1) ,(desugar e2))]
    [`(< ,e1 ,e2)
     `(> ,(desugar e2) ,(desugar e1))]
    [`(<= ,e1 ,e2)
     `(>= ,(desugar e2) ,(desugar e1))]
    [`(!= ,e1 ,e2)
     `(not (= ,(desugar e1) ,(desugar e2)))]
    [`(= ,e1 ,e2)
     `(= ,(desugar e1) ,(desugar e2))]
    ; Logical operators
    [`(and ,e1 ,e2)
     `(and ,(desugar e1) ,(desugar e2))]
    [`(or ,e1 ,e2)
     `(or ,(desugar e1) ,(desugar e2))]
    [`(not ,e)
     `(not ,(desugar e))]
    ; Function application
    [`(,rator ,rand)
     `(,(desugar rator) ,(desugar rand))]
    [e e]))

(define (desugar-type type)
  (match type
    ['Int '(Int #t)]
    ['Bool '(Bool #t)]
    ['Any '(Any #t)]
    [`(Int ,pred) `(Int ,(desugar-pred pred))]
    [`(Bool ,pred) `(Bool ,(desugar-pred pred))]
    [`(,atype -> ,rtype)
     `(,(desugar-type atype) -> ,(desugar-type rtype))]
    [t t]))

(define (desugar-pred pred)
  (match pred
    [`(<= ,e1 ,e2) `(>= ,e2 ,e1)]
    [`(< ,e1 ,e2)  `(>  ,e2 ,e1)]
    [`(!= ,e1 ,e2) `(not (= ,e1 ,e2))]
    [`(and ,e1 ,e2) `(and ,(desugar-pred e1) ,(desugar-pred e2))]
    [`(or ,e1 ,e2)  `(or ,(desugar-pred e1) ,(desugar-pred e2))]
    [`(not ,e) `(not ,(desugar-pred e))]
    [e e]))

;============

(module+ test
  (check-equal? (desugar-type 'Int) '(Int #t))
  (check-equal? (desugar-type 'Bool) '(Bool #t))
  (check-equal? (desugar-type '(Int -> Bool)) '((Int #t) -> (Bool #t)))
  (check-equal? (desugar-type '(Int (> _ 3))) '(Int (> _ 3)))
  (check-equal? (desugar-type '(Bool (and _ #f))) '(Bool (and _ #f)))
  )

(module+ test
  (check-equal? (desugar '(define x : Int 1))
                '(define x : (Int #t) 1))
  (check-equal? (desugar '(define (add1 [x : Int]) : Int (+ x 1)))
                '(define add1 : ((Int #t) -> (Int #t)) (lambda add1 [x : (Int #t)] : (Int #t) (+ x 1))))
  (check-match (desugar '(let ((x : Int 3)) (+ x 1)))
               `((lambda ,sym (x : (Int #t)) : (Any #t) (+ x 1)) 3))
  (check-equal? (desugar '(define (f [x : Any]) : (Any -> Any) (lambda whatever [y : Any] : Any x)))
              '(define f : ((Any #t) -> ((Any #t) -> (Any #t)))
                 (lambda f (x : (Any #t)) : ((Any #t) -> (Any #t))
                   (lambda whatever (y : (Any #t)) : (Any #t) x))))
  )

